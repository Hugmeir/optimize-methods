#define PERL_NO_GET_CONTEXT 1
#include "EXTERN.h"
#include "perl.h"

/* I know what I'm doing, I swear! (vile lies)*/
#ifdef WIN32
# include "XSUB.h"
#else /* not WIN32 */
# define PERL_CORE
# include "XSUB.h"
# undef PERL_CORE
#endif
 
#ifndef PadnameTYPE
# define PadnameTYPE(pn)         (SvPAD_TYPED(pn) ? SvSTASH(pn) : NULL)
#endif

#ifndef PadlistARRAY
# define PadlistARRAY(pl) ((PAD**)AvARRAY(pl))
# define PadlistNAMES(pl) (PadlistARRAY(pl)[0])
#endif /* !PadlistARRAY */

#define MY_CXT_KEY "optimize::methods::_guts" XS_VERSION

typedef struct {
#ifdef USE_ITHREADS
 tTHX owner; /* The interpeter that owns this variable */
#endif
 HV* finalized;
 HV* exclude;
} my_cxt_t;

START_MY_CXT

STATIC OP* myck_entersubop(pTHX_ OP *entersubop);


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

static Perl_ppaddr_t default_method_named = NULL;
static Perl_ppaddr_t default_entersub = NULL;

/* Undo the optimization
 * A normal method call looks something like
 *      entersub -> padsv -> 0 or more arguments -> method_named
 * the optimized version looks like this, instead:
 *      entersubfast -> padsv -> 0 or more arguments -> method_named_fast -> constcv
 *                                                       \ constsv
 * where the constcv holds the cv for this optimization, and constsv
 * is the magic scalar we use to check wether to pessimize
 * What we want to do is make it look back like the original
 */
OP*
THX_pessimize(pTHX_ OP* entersubop)
#define pessimize(o)    THX_pessimize(aTHX_ o)
{
    dVAR;
    OP * aop = cUNOPx(entersubop)->op_first;
    
    if (!aop->op_sibling)
        aop = cUNOPx(aop)->op_first;
        
    /* We want the second to last sibling */
    for (aop = aop->op_sibling; aop->op_sibling->op_sibling; aop = aop->op_sibling) {
    }
    
    /* Undo the optimization */
    OP *method_named = aop;
    OP *opcv         = method_named->op_sibling;
    OP *opconst      = method_named->op_next;
    
    opconst->op_next = NULL;
    
    /* We didn't call op_null() earlier on this so that
     * op_targ would still point to the correct scalar, and
     * so the scalar in the pad would not be freed.
     */
    method_named->op_type    = OP_METHOD_NAMED;
    method_named->op_ppaddr  = PL_ppaddr[OP_METHOD_NAMED];
    method_named->op_next    = opcv->op_next;
    method_named->op_sibling = opcv->op_sibling;
    
    opcv->op_next = NULL;
    opcv->op_sibling = NULL;
    
    op_free(opcv);
    op_free(opconst);
   
    entersubop->op_spare  = 0;
    entersubop->op_ppaddr = default_entersub;
    
    PL_op = method_named;

    /* Now that we've pessimzied, call the method_named OP;
     * this in turn will call back the now normal entersub.
     */
    return PL_ppaddr[OP_METHOD_NAMED](aTHX);
}


#define ENTERSUB_COMMON_DECLARATIONS   \
    dVAR; dSP; dPOPss;          \
    PERL_CONTEXT *cx;           \
    I32 gimme                   \

#define ENTERSUB_COMMON_END STMT_START {                        \
    SAVETMPS;                                                   \
    if ((cx->blk_u16 & OPpENTERSUB_LVAL_MASK) == OPpLVAL_INTRO) \
        DIE(aTHX_ "Can't modify non-lvalue subroutine call");   \
    RETURNOP(CvSTART(cv));                                      \
} STMT_END

#define ENTERSUB_COMMON_BODY \
    PADLIST * const padlist = CvPADLIST(cv); \
    PUSHBLOCK(cx, CXt_SUB, MARK); \
    PUSHSUB(cx); \
    cx->blk_sub.retop = PL_op->op_next; \
    CvDEPTH(cv)++; \
    if (CvDEPTH(cv) >= 2) { \
        PERL_STACK_OVERFLOW_CHECK(); \
        Perl_pad_push(aTHX_ padlist, CvDEPTH(cv)); \
    } \
    SAVECOMPPAD(); \
    PAD_SET_CUR_NOSAVE(padlist, CvDEPTH(cv))

#define ENTERSUB_COMMON_ARGS    STMT_START {                    \
    SSize_t items = SP - MARK;                                  \
    AV *const av = MUTABLE_AV(PAD_SVl(0));                      \
    if (AvREAL(av)) {                                           \
        /* @_ is normally not REAL--this should only ever       \
         * happen when DB::sub() calls things that modify @_ */ \
        av_clear(av);                                           \
        AvREAL_off(av);                                         \
        AvREIFY_on(av);                                         \
    }                                                           \
    cx->blk_sub.savearray = GvAV(PL_defgv);                     \
    GvAV(PL_defgv) = MUTABLE_AV(SvREFCNT_inc_simple(av));       \
    CX_CURPAD_SAVE(cx->blk_sub);                                \
    cx->blk_sub.argarray = av;                                  \
    ++MARK;                                                     \
                                                                \
    if (items - 1 > AvMAX(av)) {                                \
        SV **ary = AvALLOC(av);                                 \
        AvMAX(av) = items - 1;                                  \
        Renew(ary, items, SV*);                                 \
        AvALLOC(av) = ary;                                      \
        AvARRAY(av) = ary;                                      \
    }                                                           \
                                                                \
    Copy(MARK,AvARRAY(av),items,SV*);                           \
    AvFILLp(av) = items - 1;                                    \
                                                                \
    MARK = AvARRAY(av);                                         \
    while (items--) {                                           \
        if (*MARK) {                                            \
            if (SvPADTMP(*MARK) && !IS_PADGV(*MARK)) {          \
                *MARK = sv_mortalcopy(*MARK);                   \
            }                                                   \
            SvTEMP_off(*MARK);                                  \
        }                                                       \
        MARK++;                                                 \
    }                                                           \
} STMT_END

#define ENTERSUB_XS_ARGS STMT_START {   \
    SSize_t markix = TOPMARK;           \
    SAVETMPS;                           \
    PUTBACK;                            \
    if (((PL_op->op_private                                     \
           & PUSHSUB_GET_LVALUE_MASK(Perl_is_lvalue_sub)        \
             ) & OPpENTERSUB_LVAL_MASK) == OPpLVAL_INTRO &&     \
        !CvLVALUE(cv))                                          \
        DIE(aTHX_ "Can't modify non-lvalue subroutine call");   \
    SV **mark = PL_stack_base + markix; \
    SSize_t items = SP - mark;          \
    while (items--) {                   \
        mark++;                         \
        if (*mark && SvPADTMP(*mark) && !IS_PADGV(*mark)) { \
            *mark = sv_mortalcopy(*mark);                   \
        }                               \
    }                                   \
    assert(CvXSUB(cv));                 \
    CvXSUB(cv)(aTHX_ cv);               \
    if (gimme == G_SCALAR && ++markix != PL_stack_sp - PL_stack_base ) {    \
        if (markix > PL_stack_sp - PL_stack_base)                           \
        *(PL_stack_base + markix) = &PL_sv_undef;                           \
        else                                                                \
        *(PL_stack_base + markix) = *PL_stack_sp;                           \
        PL_stack_sp = PL_stack_base + markix;                               \
    }                                                                       \
    LEAVE;                              \
    return NORMAL;                      \
} STMT_END

/* foo() */
STATIC OP*
S_pp_entersubcv_args(pTHX)
{
    ENTERSUB_COMMON_DECLARATIONS;
    CV *cv = MUTABLE_CV(sv);
    const bool hasargs = TRUE;

    ENTER;

    gimme = GIMME_V;

    dMARK;

    ENTERSUB_COMMON_BODY;

    /* Handle arguments */
    ENTERSUB_COMMON_ARGS;

    ENTERSUB_COMMON_END;
}


/* foo() */
STATIC OP*
S_pp_entersubcvxs_args(pTHX)
{
    ENTERSUB_COMMON_DECLARATIONS;
    CV *cv = MUTABLE_CV(sv);
    const bool hasargs = TRUE;

    ENTER;

    gimme = GIMME_V;

    /* Handle arguments */
    ENTERSUB_XS_ARGS;
}

OP *
om_method_named_fast(pTHX)
{
    dVAR; dSP;
    OP * constcv    = PL_op->op_sibling;
    OP * entersubop = PL_op->op_next->op_next;
    SV * saved_sv   = cSVOPx_sv(PL_op->op_next);
    SV * obj_sv     = *(PL_stack_base + TOPMARK + 1);

    if (!obj_sv || obj_sv == &PL_sv_undef)
        return pessimize(entersubop);
    
    SvGETMAGIC(obj_sv);

    if (!SvROK(obj_sv)) {
        /* my $x = "Foo"; $x->bar */
        if (isGV_with_GP(obj_sv)) {
            /* Still don't care. */
            return pessimize(entersubop);
        }
        else {
            STRLEN len;
            STRLEN obj_class_len;
            const char *classname = SvPV_nomg_const(obj_sv, obj_class_len);
            const char *pv = SvPV_nomg_const(saved_sv, len);
            if (len != obj_class_len
                || memNE(pv, classname, len))
            {
                return pessimize(entersubop);
            }
        }
    }
    else {
        SV *ob = MUTABLE_SV(SvRV(obj_sv));
        
        if (!ob || !(SvOBJECT(ob))) {
            return pessimize(entersubop);
        }

        HV *stash      = SvSTASH(ob);
        HV *orig_stash = INT2PTR(HV*, SvIV(saved_sv));
        /* This is not exactly safe, but chances of it
            * going badly are miniscule
            */
        if (orig_stash != stash) {
            /* Compare names. If they are the same, then
                * threads happened
                */
            STRLEN len;
            const char *classname = HvNAME(stash);
            const char *pv = SvPV_nomg_const(saved_sv, len);
            if (len == (STRLEN)HvNAMELEN(stash)
                && memEQ(pv, classname, len))
            {
                SvIV_set(saved_sv, PTR2IV(stash));
            }
            else {
                return pessimize(entersubop);
            }
        }
    }

    XPUSHs(cSVOPx_sv(constcv));
    PUTBACK;

    return entersubop;
}

OP *
om_method_named(pTHX) {
    dVAR;

    /* We need to call the default method_named first! */

    OP *entersubop = default_method_named(aTHX);
    SV *sv = *PL_stack_sp;

    if (sv && (SvTYPE(sv) == SVt_PVCV) && !CvLVALUE(sv))
    {
        OP * method_named = PL_op;
        SV * obj_sv       = *(PL_stack_base + TOPMARK + 1);
        SV * newsv;
        
        SvGETMAGIC(obj_sv);
        if (!SvROK(obj_sv)) {
            if (isGV_with_GP(obj_sv)) {
                /* *foo->bar */
                HV * stash = GvSTASH(obj_sv);
                newsv = newSVhek(HvNAME_HEK(stash));
                (void)SvUPGRADE(newsv, SVt_PVNV);
                SvIV_set(newsv, PTR2IV(stash));
                SvIOK_on(newsv);
            }
            else {
                /* $x = "Foo"; $x->bar */
                newsv = newSVsv(obj_sv);
                (void)SvUPGRADE(newsv, SVt_PVNV);
                SvIV_set(newsv, 0);
                SvIOK_on(newsv);
            }
        }
        else {
            /* Either a blessed object or a reference to a glob */
            SV * ob    = SvRV(obj_sv);
            HV * stash = SvOBJECT(ob) ? SvSTASH(ob) : GvSTASH(ob);
            newsv = newSVhek(HvNAME_HEK(stash));
            (void)SvUPGRADE(newsv, SVt_PVNV);
            SvIV_set(newsv, PTR2IV(stash));
            SvIOK_on(newsv);
        }
        
        /* What we have:
         *  entersub -> padsv -> ... -> method_named ->> entersubfast
         * we want:
         *  entersubfast -> padsv -> ... -> method_named_fast -> cv ->> entersubfast
         *                                      \->> op_const
         */
        OP * opconst = newSVOP(OP_CONST, 0, newsv);
        SV * cv      = SvREFCNT_inc_simple_NN(MUTABLE_CV(sv));
        OP * new_op  = newSVOP(OP_CONST, 0, cv);
        
        opconst->op_next = entersubop;
        
        new_op->op_sibling = method_named->op_sibling;
        new_op->op_next    = method_named->op_next;

        /* Do NOT touch op_targ! */
        method_named->op_next    = opconst;
        method_named->op_ppaddr  = om_method_named_fast;
        method_named->op_sibling = new_op;

        entersubop->op_ppaddr = CvISXSUB(cv)
                              ? S_pp_entersubcvxs_args
                              : S_pp_entersubcv_args;
        return entersubop;
    }
    else {
        PL_op->op_ppaddr = PL_ppaddr[OP_METHOD_NAMED];
        return entersubop;
    }
}

STATIC void
THX_optimize_named_method(pTHX_ OP *entersubop, AV * const comppad_name)
#define optimize_named_method(o, av) THX_optimize_named_method(aTHX_ o, av)
{
    OP * aop = cUNOPx(entersubop)->op_first;
    HV * stash;
    SV * class_sv;
    const bool hasargs = (entersubop->op_flags & OPf_STACKED) != 0;

    /* hasargs is really wether a subroutine is being called
     * ala &foo, which is never true with methods. So bail out
     * of this one quickly.
     */
    if (!hasargs) {
        return;
    }
    
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
    if ( aop->op_type != OP_METHOD_NAMED ) {
        return;
    }
    
    if ( (stash = method_named_find_stash(classname_op, comppad_name, &class_sv)) ) {
        dMY_CXT;
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

        {
        CV *cv;
        SV *method;
        GV *gv;

        /* Get the method name from the method_named op */
        method = cSVOPx_sv(aop);

        gv = gv_fetchmethod_sv_flags(stash, method, 0);
        if ( gv && isGV(gv) && (cv = GvCV(gv))
            /* All bets are off if the CV has magic attached */
            && !CvANON(cv) && !SvMAGIC((SV*)cv) )
        {
            /* We MUST use CvGV(cv) here, NOT gv. This is because
             * the GV might be Doof::bar, but the CV actually resides
             * in Foo::bar; CvGV(cv) will give us the right location.
             * ...except for anon subs, which will give us something
             * unfindable, like Foo::__ANON__
             */
            GV * last_gv    = CvANON(cv) ? gv : CvGV(cv);
            OP * new_op     = newGVOP(OP_GV, 0, last_gv);
            new_op->op_next = entersubop;
            
            /* This can be catastrophic if dealing
             * with threads; the op may change while a
             * sub is running
             */
            OP_REFCNT_LOCK;
            aop->op_next          = new_op;
            op_null(aop);
            aop->op_sibling       = aop->op_next;
            cUNOPx(aop)->op_first = aop->op_next;
            OP_REFCNT_UNLOCK;

            /* Finally, since the classname is now an argument, it's subject
             * to strict checking, so turn it off for this bareword
             */
            if ( classname_op->op_type == OP_CONST ) {
                classname_op->op_private &= ~(OPpCONST_BARE|OPpCONST_STRICT);
            }
        }
        else {
            /* Late binding */
            if ( gv && MUTABLE_SV(gv) == &PL_sv_yes ) {
                /* ->import and ->unimport, don't care */;
            }
            else {
                /* Try the runtime optimization, but is it worth it?
                 * This is around 2% of all method calls
                 */
                aop->op_ppaddr = om_method_named;            
            }

            /*
            if (gv && MUTABLE_SV(gv) != &PL_sv_yes && !cv) {
                //PerlIO_printf(Perl_debug_log, "\nShould never happen: %"SVf"->%"SVf"\n", newSVhek(HvNAME_HEK(stash)), method);
            }
            else if (!gv) {
                
                //PerlIO_printf(Perl_debug_log, "WOah: %"SVf"->%"SVf"\n", newSVhek(HvNAME_HEK(stash)), method);
            }
            */
        }
        }
    }
    else {
        /* Experiment time!
            * Try changing $foo->bar() into
            * Class::bar($foo) at runtime, and pessimize if
            * $foo is ever of a different class.
            * This also grabs several "hard" cases, like
            * bless(..)->foo, sub {...}->foo, $x[0]->foo,
            * $x{foo}->foo, etc
         */
        aop->op_ppaddr = om_method_named;
    }
}


STATIC void
THX_padop_assign_type(pTHX_ OP* padsv, HV* stash)
#define padop_assign_type(padsv, stash) THX_padop_assign_type(aTHX_ padsv, stash)
{
    SV **svp;
    
    if ( !PL_comppad_name || !SvOK(PL_comppad_name) ) {
       /* Global destruction */
        return;
    }

    svp = av_fetch(PL_comppad_name, padsv->op_targ, FALSE);

    if (!svp || !*svp)
        return;
    SV *assign_sv = *svp;
    if (!PadnameTYPE(assign_sv)) {
        if (SvTYPE(assign_sv) != SVt_PVMG) {
            SvUPGRADE(assign_sv, SVt_PVMG);
        }
        
        SvPAD_TYPED_on(assign_sv);
        SvSTASH_set(assign_sv, MUTABLE_HV(SvREFCNT_inc_simple_NN(MUTABLE_SV(stash))));
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
    /* If the last sibling isn't a method call op, then return */
    if ( aop->op_type != OP_METHOD_NAMED && aop->op_type != OP_METHOD ) {
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

    padop_assign_type(padsv, stash);
}

static OP *(*nxck_entersubop)(pTHX_ OP *o);
static OP *(*nxck_sassign)(pTHX_ OP *o);

STATIC OP*
myck_sassign(pTHX_ OP *o)
{
    OP *first= cLISTOPo->op_first;
    
    if (first) {
    switch (first->op_type) {
        case OP_ENTERSUB: {
            /* Turn 
             * my $foo = Foo->new();
             * into
             * my Foo $foo = Foo->new()
             * which allows any later uses of $foo->method_call()
             * to be optimized
             */
            typefy_pad_entries(first);
            break;
        }
        case OP_BLESS: {
            /* Typefy $x = bless {}, "Foo" */
            HV *stash;
            OP *target = first->op_sibling;

            if ( !target || target->op_type != OP_PADSV ) {
                break;
            }
            
            OP *classname_op = cLISTOPx(first)->op_last;
            
            /* bless {}; */
            if ( cLISTOPx(first)->op_first->op_sibling == classname_op ) {
                stash = PL_curstash;
            }
            /* bless {}, "Foo"; */
            else if ( classname_op->op_type == OP_CONST ) {
                SV *class = cSVOPx_sv(classname_op);
                stash     = gv_stashsv(class, 0);
                
            }
            
            if (stash) {
                padop_assign_type(target, stash);
            }
            break;
        }
        case OP_PADSV: {
            /* Turn
             * my $y = $x;
             * when $x is a typed lexical into
             * my type $y = $x;
             */
            /* An intriging experiment. Also useless, nothing does this */
            OP *target = first->op_sibling;

            if ( !target || target->op_type != OP_PADSV ) {
                break;
            }

            /* We're handling something like $x = $y;
             * Let's check if $y is typed; if it is, we
             * can copy its type to $x
             */
             
            SV **svp = av_fetch(PL_comppad_name, target->op_targ, FALSE);
            SV *from_sv;
            SV *target_sv;
            HV *stash;
            
            if (!svp || !*svp)
                break;

            target_sv = *svp;
            if (PadnameTYPE(target_sv)) {
                /* The target is already typed, skip doing anything */
                break;
            }
            
            svp = av_fetch(PL_comppad_name, first->op_targ, FALSE);
            if (!svp || !*svp)
                break;
                
            from_sv = *svp;
            if (!(stash = PadnameTYPE(from_sv))) {
                break;
            }
            
            padop_assign_type(target, stash);
            break;
        }
    }
    }
    
    
    return nxck_sassign(aTHX_ o);
}

STATIC OP*
myck_entersubop(pTHX_ OP *entersubop)
{
    /* Be nice and let others do their work first */
    OP * o = nxck_entersubop(aTHX_ entersubop);
    optimize_named_method(o, PL_comppad_name);
    
    return entersubop;
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
    
    nxck_entersubop       = PL_check[OP_ENTERSUB];
    
    default_entersub      = PL_ppaddr[OP_ENTERSUB];
    default_method_named  = PL_ppaddr[OP_METHOD_NAMED];
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
        MY_CXT.exclude   = exclude_clone;
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
start(SV *classname)
CODE:
    PL_check[OP_SASSIGN]  = myck_sassign;
    PL_check[OP_ENTERSUB] = myck_entersubop;

void
done(SV *classname)
CODE:
    PL_check[OP_SASSIGN]  = nxck_sassign;
    PL_check[OP_ENTERSUB] = nxck_entersubop;


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

