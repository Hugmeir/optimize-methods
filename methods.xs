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
} my_cxt_t;

START_MY_CXT


STATIC void
optimize_named_method(pTHX_ OP *entersubop, AV * const comppad_name)
#define optimize_named_method(o, av) optimize_named_method(aTHX_ o, av)
{
    OP * aop = cUNOPx(entersubop)->op_first;
    SV * class_sv;
    HV * stash;

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

    /* If the last sibling isn't a method_named op, then return */
    if ( aop->op_type != OP_METHOD_NAMED )
        return;

    if ( classname_op->op_type == OP_CONST ) {
        STRLEN len;
        class_sv = cSVOPx_sv(classname_op);
        /* Disallow ""->doof() */
        if ( !*(SvPV(class_sv, len)) || len == 0 )
            return;
        stash = gv_stashsv(class_sv, 0);
    }
    /* Typed lexicals */
    else if ( classname_op->op_type == OP_PADSV ) {
        SV **svp = av_fetch(comppad_name, classname_op->op_targ, FALSE);
        if (!svp || !*svp)
            return;
        class_sv = *svp;
        if (!class_sv || !(stash = PadnameTYPE(class_sv)))
            return;
        class_sv = newSVhek(HvNAME_HEK(stash));
    }
    else {
        return;
    }

    if ( stash ) {
        dMY_CXT;
        CV *cv;
        SV *method;
        GV *gv;
        HV *finalized = MY_CXT.finalized;

        /* If :all is there, then go ahead and try to optimize this;
         * otherwise, we need to check if this class was marked as
         * finalized
         */
        if ( !hv_fetchs(finalized, ":all", FALSE)
          && !hv_fetch_ent(finalized, class_sv, 0, 0))
        {
            return;
        }

        /* Get the method name from the method_named op */
        method = cSVOPx_sv(aop);
        gv   = gv_fetchmethod_sv_flags(stash, method, 0);
        if ( gv && isGV(gv) && (cv = GvCV(gv)) ) {
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
            aop->op_next    = new_op;
            op_null(aop);
            aop->op_sibling = aop->op_next;
            OP_REFCNT_UNLOCK;
        }
    }
}


static OP *(*nxck_entersubop)(pTHX_ OP *o);

#define CK_RETURN 
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
    
    nxck_entersubop       = PL_check[OP_ENTERSUB];
    PL_check[OP_ENTERSUB] = myck_entersubop;
}

#ifdef USE_ITHREADS
 
void
CLONE(...)
INIT:
    HV * finalized_clone = NULL;
CODE:
{
    PERL_UNUSED_ARG(items);
    {
        dMY_CXT;
        tTHX owner = MY_CXT.owner;
         
        finalized_clone = clone_hv(MY_CXT.finalized, owner);
    }
    {
        MY_CXT_CLONE;
        MY_CXT.finalized = finalized_clone;
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

