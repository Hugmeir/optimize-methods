#define PERL_NO_GET_CONTEXT 1
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"


#define MY_CXT_KEY "optimize::methods::_guts" XS_VERSION

typedef struct {
#ifdef USE_ITHREADS
 tTHX owner; /* The interpeter that owns this variable */
#endif
 HV* finalized;
 HV* exclude;
} my_cxt_t;

START_MY_CXT


#ifndef PadnamelistMAXNAMED
# define PadnamelistMAXNAMED(pnl) \
	((XPVAV*) SvANY(pnl))->xmg_u.xmg_hash_index
#endif

STATIC HV*
THX_method_named_find_stash(pTHX_ OP *classname_op, AV * const comppad_name, SV **class_sv)
#define method_named_find_stash(o,pad,sv) THX_method_named_find_stash(aTHX_ o,pad,sv)
{
    HV *stash;
    if ( classname_op->op_type == OP_CONST ) {
        STRLEN len;
        *class_sv = cSVOPx_sv(classname_op);
        /* Disallow ""->doof() */
        if ( !*class_sv || !*(SvPV(*class_sv, len)) || len == 0 )
            return NULL;
        stash = gv_stashsv(*class_sv, 0);
        return stash;
    }
    /* Typed lexicals */
    else if ( classname_op->op_type == OP_PADSV ) {
        SV **svp = av_fetch(comppad_name, classname_op->op_targ, FALSE);
        if (!svp || !*svp)
            return NULL;
        *class_sv = *svp;
        if (!*class_sv || !(stash = PadnameTYPE(*class_sv))) {
            return NULL;
        }
        if ( !HvNAME_HEK(stash) ) {
            /* Should never happen */
            return NULL;
        }
        *class_sv  = newSVhek(HvNAME_HEK(stash));
        return stash;
    }
    else {
        return NULL;
    }
}

STATIC void
THX_optimize_named_method(pTHX_ OP *entersubop, AV * const comppad_name)
#define optimize_named_method(o, av) THX_optimize_named_method(aTHX_ o, av)
{
    OP * aop = cUNOPx(entersubop)->op_first;
    HV * stash;
    SV * class_sv;

    if (!aop->op_sibling)
       aop = cUNOPx(aop)->op_first;

    OP *classname_op = aop->op_sibling;

    /* This sub has no arguments, ergo no classname/object -- so it's not
     * a method call */
    if ( !classname_op )
        return;

    /* We want the last sibling */
    for (aop = aop->op_sibling; aop->op_sibling; aop = aop->op_sibling) {
    }

    if ( classname_op->op_type == OP_ENTERSUB ) {
        return;
    }

    /* If the last sibling isn't a method_named op, then return */
    if ( aop->op_type != OP_METHOD_NAMED ) {
        return;
    }

    if ( (stash = method_named_find_stash(classname_op, comppad_name, &class_sv)) ) {
        dMY_CXT;
        CV *cv;
        SV *method;
        GV *gv;
        HV *finalized = MY_CXT.finalized;
        HV *exclude   = MY_CXT.exclude;

        /* If :all is there, then go ahead and try to optimize this;
         * otherwise, we need to check if this class was marked as
         * finalized
         */
        if ( !hv_fetchs(finalized, ":all", FALSE)
          && !hv_fetch_ent(finalized, class_sv, 0, 0))
        {
            return;
        }
        
        if ( hv_fetch_ent(exclude, class_sv, 0, 0) ) {
            return;
        }
        
        /* Get the method name from the method_named op */
        method = cSVOPx_sv(aop);

        gv   = gv_fetchmethod_sv_flags(stash, method, 0);
        if ( gv && isGV(gv) && (cv = GvCV(gv))
            /* XXX Find out why these two are necessary! */
            && !CvANON(cv) && !SvMAGIC((SV*)cv) )
        {
            /* We MUST use CvGV(cv) here, NOT gv. This is because
             * the GV might be Doof::bar, but the CV actually resides
             * in Foo::bar; CvGV(cv) will give us the right location.
             */
            OP * new_op     = newGVOP(OP_GV, 0, CvGV(cv));
            new_op->op_next = entersubop;
            
            /* This can be catastrophic if dealing
             * with threads; the op may change while a
             * sub is running
             */
            OP_REFCNT_LOCK;
            aop->op_next          = new_op;
            op_null(aop);
            //aop->op_sibling       = aop->op_next;
            cUNOPx(aop)->op_first = aop->op_next;
            OP_REFCNT_UNLOCK;

            /* Finally, since the classname is now an argument, it's subject
             * to strict checking, so turn it off for this bareword
             */
            classname_op->op_private &= ~(OPpCONST_BARE|OPpCONST_STRICT);
        }
    }
}

STATIC void
THX_typefy_pad_entries(pTHX_ OP* entersubop)
#define typefy_pad_entries(o) THX_typefy_pad_entries(aTHX_ o)
{
    OP * padsv;
    OP * aop;
    HV * stash;
    SV * class_sv;

    aop = cUNOPx(entersubop)->op_first;
    if (!aop->op_sibling)
       aop = cUNOPx(aop)->op_first;

    OP *classname_op = aop->op_sibling;

    if ( !classname_op )
        return;

    /* We want the last sibling */
    for (aop = aop->op_sibling; aop->op_sibling; aop = aop->op_sibling) {
    }
    /* If the last sibling isn't a method_named op, then return */
    if ( aop->op_type != OP_METHOD_NAMED ) {
        OP *opgv;
        if ( ((aop->op_type == OP_NULL
            && aop->op_targ == OP_METHOD_NAMED
            && (opgv = cUNOPx(aop)->op_first))
            || (aop->op_type == OP_GV && (opgv = aop)))
            && opgv->op_type == OP_GV )
        {
            /* the method_named was optimized away */
            GV *gv   = cGVOPx_gv(opgv);
            CV *cv   = GvCV(gv);
            stash    = CvSTASH(cv);
            if (!stash)
                return;
        }
        else {
            return;
        }
    }
    else {
        stash = method_named_find_stash(classname_op, PL_comppad_name, &class_sv);
    }
    if (!stash)
        return;

    padsv = entersubop->op_sibling;

    if ( !padsv || padsv->op_type != OP_PADSV ) {
        return;
    }

    SV **svp = av_fetch(PL_comppad_name, padsv->op_targ, FALSE);
    if (!svp || !*svp)
        return;
    SV *assign_sv = *svp;
    if (assign_sv && !PadnameTYPE(assign_sv)) {
        if (SvTYPE(assign_sv) != SVt_PVMG) {
            SvUPGRADE(assign_sv, SVt_PVMG);
        }

        SvPAD_TYPED_on(assign_sv);
        SvSTASH_set(assign_sv, MUTABLE_HV(SvREFCNT_inc_simple_NN(MUTABLE_SV(stash))));
        av_store(PL_comppad_name, padsv->op_targ, SvREFCNT_inc_simple_NN(assign_sv));

        if ( PadnamelistMAXNAMED(PL_comppad_name) < padsv->op_targ ) {
            PadnamelistMAXNAMED(PL_comppad_name) = padsv->op_targ;
        }
    }
}

static OP *(*nxck_entersubop)(pTHX_ OP *o);
static OP *(*nxck_sassign)(pTHX_ OP *o);

STATIC OP*
myck_sassign(pTHX_ OP *o)
{
    OP *entersubop = cLISTOPo->op_first;
    
    if (entersubop && entersubop->op_type == OP_ENTERSUB) {
        typefy_pad_entries(entersubop);
    }
    
    return nxck_sassign(aTHX_ o);
}

STATIC OP*
myck_entersubop(pTHX_ OP *entersubop)
{
    optimize_named_method(entersubop, PL_comppad_name);
    
    return nxck_entersubop(aTHX_ entersubop);
}

#ifdef USE_ITHREADS
STATIC SV*
clone_sv(pTHX_ SV* sv, tTHX owner)
#define clone_sv(s,v) clone_sv(aTHX_ (s), (v))
{
    CLONE_PARAMS param;
    param.stashes    = NULL;
    param.flags      = 0;
    param.proto_perl = owner;
 
    return sv_dup_inc(sv, &param);
}
 
#define clone_hv(s,v) MUTABLE_HV(clone_sv((SV*)(s), (v)))
#endif /* USE_ITHREADS */

MODULE = optimize::methods PACKAGE = optimize::methods

PROTOTYPES: DISABLE

BOOT:
{
    MY_CXT_INIT;
    MY_CXT.finalized = newHV();
    MY_CXT.exclude   = newHV();
    
    nxck_sassign          = PL_check[OP_SASSIGN];
    PL_check[OP_SASSIGN]  = myck_sassign;
    
    nxck_entersubop       = PL_check[OP_ENTERSUB];
    PL_check[OP_ENTERSUB] = myck_entersubop;
}

#ifdef USE_ITHREADS
 
void
CLONE(...)
INIT:
    HV * finalized_clone = NULL;
    HV * exclude_clone   = NULL;
CODE:
{
    PERL_UNUSED_ARG(items);
    {
        dMY_CXT;
        tTHX owner = MY_CXT.owner;
         
        finalized_clone = clone_hv(MY_CXT.finalized, owner);
        exclude_clone   = clone_hv(MY_CXT.exclude, owner);
    }
    {
        MY_CXT_CLONE;
        MY_CXT.finalized = finalized_clone;
        NY_CXT.exclude   = exclude_clone;
        MY_CXT.owner     = aTHX;
    }
}
 
#endif /* USE_ITHREADS */

void
optimize_methods(SV *classname)
CODE:
    dMY_CXT;
    (void) hv_store_ent(MY_CXT.finalized, classname, &PL_sv_yes, 0);


void
unfinalize_class(SV *classname)
CODE:
    dMY_CXT;
    (void) hv_delete_ent(MY_CXT.finalized, classname, G_DISCARD, 0);

void
exclude_class(SV *classname)
CODE:
    dMY_CXT;
    (void) hv_store_ent(MY_CXT.exclude, classname, &PL_sv_yes, 0);


void
traverse_function(SV *sv)
CODE:
    CV *cv = MUTABLE_CV(SvRV(sv));
    OP *o  = CvROOT(cv);
    
    o = cUNOPx(cUNOPx(o)->op_first)->op_first;

    for (; o; o = o->op_next) {
        if (o->op_type == OP_ENTERSUB) {
            const PADLIST * const padlist = CvPADLIST(cv);
            AV * const comppad_name = PadlistARRAY(padlist)[0];
            optimize_named_method(o, comppad_name);
        }
    }

