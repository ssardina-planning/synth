#ifdef __cplusplus
extern "C" {
#endif
#include "util.h"
#include "cudd/cudd.h"
#undef EXTERN
#undef ARGS
#undef assert
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"
#ifdef __cplusplus
}
#endif

static int
not_here(s)
char *s;
{
    croak("%s not implemented on this architecture", s);
    return -1;
}

static double
constant(name, arg)
char *name;
int arg;
{
    errno = 0;
    switch (*name) {
    case 'A':
	if (strEQ(name, "APA_BASE"))
#ifdef DD_APA_BASE
	    return DD_APA_BASE;
#else
	    goto not_there;
#endif
	if (strEQ(name, "APA_BITS"))
#ifdef DD_APA_BITS
	    return DD_APA_BITS;
#else
	    goto not_there;
#endif
	if (strEQ(name, "APA_MASK"))
#ifdef DD_APA_MASK
	    return DD_APA_MASK;
#else
	    goto not_there;
#endif
	break;
    case 'C':
	if (strEQ(name, "CACHE_SLOTS"))
#ifdef CUDD_CACHE_SLOTS
	    return CUDD_CACHE_SLOTS;
#else
	    goto not_there;
#endif
	break;
    case 'M':
	if (strEQ(name, "MAXINDEX"))
#ifdef CUDD_MAXINDEX
	    return CUDD_MAXINDEX;
#else
	    goto not_there;
#endif
	if (strEQ(name, "MTR_DEFAULT"))
#ifdef MTR_DEFAULT
	    return MTR_DEFAULT;
#else
	    goto not_there;
#endif
	if (strEQ(name, "MTR_FIXED"))
#ifdef MTR_FIXED
	    return MTR_FIXED;
#else
	    goto not_there;
#endif
	break;
    case 'O':
	if (strEQ(name, "OUT_OF_MEM"))
#ifdef CUDD_OUT_OF_MEM
	    return CUDD_OUT_OF_MEM;
#else
	    goto not_there;
#endif
	break;
    case 'R':
	if (strEQ(name, "REORDER_SAME"))
	    return CUDD_REORDER_SAME;
	if (strEQ(name, "REORDER_NONE"))
	    return CUDD_REORDER_NONE;
	if (strEQ(name, "REORDER_RANDOM"))
	    return CUDD_REORDER_RANDOM;
	if (strEQ(name, "REORDER_RANDOM_PIVOT"))
	    return CUDD_REORDER_RANDOM_PIVOT;
	if (strEQ(name, "REORDER_SIFT"))
	    return CUDD_REORDER_SIFT;
	if (strEQ(name, "REORDER_SIFT_CONVERGE"))
	    return CUDD_REORDER_SIFT_CONVERGE;
	if (strEQ(name, "REORDER_SYMM_SIFT"))
	    return CUDD_REORDER_SYMM_SIFT;
	if (strEQ(name, "REORDER_SYMM_SIFT_CONV"))
	    return CUDD_REORDER_SYMM_SIFT_CONV;
	if (strEQ(name, "REORDER_WINDOW2"))
	    return CUDD_REORDER_WINDOW2;
	if (strEQ(name, "REORDER_WINDOW3"))
	    return CUDD_REORDER_WINDOW3;
	if (strEQ(name, "REORDER_WINDOW4"))
	    return CUDD_REORDER_WINDOW4;
	if (strEQ(name, "REORDER_WINDOW2_CONV"))
	    return CUDD_REORDER_WINDOW2_CONV;
	if (strEQ(name, "REORDER_WINDOW3_CONV"))
	    return CUDD_REORDER_WINDOW3_CONV;
	if (strEQ(name, "REORDER_WINDOW4_CONV"))
	    return CUDD_REORDER_WINDOW4_CONV;
	if (strEQ(name, "REORDER_GROUP_SIFT"))
	    return CUDD_REORDER_GROUP_SIFT;
	if (strEQ(name, "REORDER_GROUP_SIFT_CONV"))
	    return CUDD_REORDER_GROUP_SIFT_CONV;
	if (strEQ(name, "REORDER_ANNEALING"))
	    return CUDD_REORDER_ANNEALING;
	if (strEQ(name, "REORDER_GENETIC"))
	    return CUDD_REORDER_GENETIC;
	if (strEQ(name, "REORDER_LINEAR"))
	    return CUDD_REORDER_LINEAR;
	if (strEQ(name, "REORDER_LINEAR_CONVERGE"))
	    return CUDD_REORDER_LINEAR_CONVERGE;
	if (strEQ(name, "REORDER_EXACT"))
	    return CUDD_REORDER_EXACT;
	if (strEQ(name, "RESIDUE_DEFAULT"))
#ifdef CUDD_RESIDUE_DEFAULT
	    return CUDD_RESIDUE_DEFAULT;
#else
	    goto not_there;
#endif
	if (strEQ(name, "RESIDUE_MSB"))
#ifdef CUDD_RESIDUE_MSB
	    return CUDD_RESIDUE_MSB;
#else
	    goto not_there;
#endif
	if (strEQ(name, "RESIDUE_TC"))
#ifdef CUDD_RESIDUE_TC
	    return CUDD_RESIDUE_TC;
#else
	    goto not_there;
#endif
	break;
    case 'S':
	if (strEQ(name, "SIZEOF_INT"))
#ifdef SIZEOF_INT
	    return SIZEOF_INT;
#else
	    goto not_there;
#endif
	if (strEQ(name, "SIZEOF_LONG"))
#ifdef SIZEOF_LONG
	    return SIZEOF_LONG;
#else
	    goto not_there;
#endif
	if (strEQ(name, "SIZEOF_VOID_P"))
#ifdef SIZEOF_VOID_P
	    return SIZEOF_VOID_P;
#else
	    goto not_there;
#endif
	break;
    case 'U':
	if (strEQ(name, "UNIQUE_SLOTS"))
#ifdef CUDD_UNIQUE_SLOTS
	    return CUDD_UNIQUE_SLOTS;
#else
	    goto not_there;
#endif
	break;
    }
    errno = EINVAL;
    return 0;

not_there:
    errno = ENOENT;
    return 0;
}


MODULE = Cudd		PACKAGE = Cudd		PREFIX = Cudd_

PROTOTYPES: ENABLE

double
constant(name,arg)
	char *		name
	int		arg

DdManager *
Cudd_Init(numVars = 0, numVarsZ = 0, numSlots = 251, cacheSize = 131071, maxMemory = 0)
	unsigned int numVars
	unsigned int numVarsZ
	unsigned int numSlots
	unsigned int cacheSize
	unsigned int maxMemory

void
Cudd_Quit(unique)
	DdManager*	unique

void
Cudd_Ref(n)
	DdNode*		n

void
Cudd_RecursiveDeref(table,n)
	DdManager*	table
	DdNode*		n

void
Cudd_IterDerefBdd(table,n)
	DdManager*	table
	DdNode*		n

void
Cudd_DelayedDerefBdd(table,n)
	DdManager*	table
	DdNode*		n

DdNode *
Cudd_ReadOne(dd)
	DdManager*	dd

int
Cudd_DagSize(node)
	DdNode*		node

double
Cudd_CountMinterm(manager, node, nvars)
	DdManager*	manager
	DdNode*		node
	int		nvars

int
Cudd_PrintDebug(dd, f, n, pr)
	DdManager*	dd
	DdNode*		f
	int		n
	int		pr

int
Cudd_PrintInfo(dd)
	DdManager*	dd
CODE:
	RETVAL = Cudd_PrintInfo(dd,stdout);
OUTPUT:
	RETVAL

int
Cudd_ReadPeakLiveNodeCount(dd)
	DdManager*	dd

int
Cudd_ReadNodeCount(dd)
	DdManager*	dd

DdNode *
Cudd_bddNewVar(dd)
	DdManager*	dd

DdNode *
Cudd_bddNewVarAtLevel(dd, level)
	DdManager*	dd
	int		level

int
Cudd_MakeTreeNode(dd, low, size, type = MTR_DEFAULT)
	DdManager*	dd
	unsigned int	low
	unsigned int	size
	unsigned int	type
PREINIT:
	MtrNode *node;
CODE:
	node = Cudd_MakeTreeNode(dd, low, size, type);
	RETVAL = node != NULL;
OUTPUT:
	RETVAL

DdNode *
Cudd_bddAnd(dd, f, g)
	DdManager*	dd
	DdNode*		f
	DdNode*		g

DdNode *
Cudd_bddOr(dd, f, g)
	DdManager*	dd
	DdNode*		f
	DdNode*		g

DdNode *
Cudd_bddXor(dd, f, g)
	DdManager*	dd
	DdNode*		f
	DdNode*		g

DdNode *
Cudd_bddXnor(dd, f, g)
	DdManager*	dd
	DdNode*		f
	DdNode*		g

DdNode *
Cudd_bddNand(dd, f, g)
	DdManager*	dd
	DdNode*		f
	DdNode*		g

DdNode *
Cudd_bddNor(dd, f, g)
	DdManager*	dd
	DdNode*		f
	DdNode*		g

DdNode *
Cudd_bddConstrain(dd, f, c)
	DdManager*	dd
	DdNode*		f
	DdNode*		c

DdNode *
Cudd_bddRestrict(dd, f, c)
	DdManager*	dd
	DdNode*		f
	DdNode*		c

DdNode *
Cudd_bddSqueeze(dd, l, u)
	DdManager*	dd
	DdNode*		l
	DdNode*		u

DdNode *
Cudd_bddExistAbstract(manager, f, cube)
	DdManager*	manager
	DdNode*		f
	DdNode*		cube

DdNode *
Cudd_bddAndAbstract(manager, f, g, cube)
	DdManager*	manager
	DdNode*		f
	DdNode*		g
	DdNode*		cube

DdNode *
Cudd_bddUnivAbstract(manager, f, cube)
	DdManager*	manager
	DdNode*		f
	DdNode*		cube

DdNode *
Cudd_bddCompose(dd, f, g, v)
	DdManager*	dd
	DdNode*		f
	DdNode*		g
	int		v

DdNode *
Cudd_bddBooleanDiff(manager, f, x)
	DdManager*	manager
	DdNode*		f
	int		x

double
Cudd_bddCorrelation(manager, f, g)
	DdManager*	manager
	DdNode*		f
	DdNode*		g

int
Cudd_Decreasing(dd, f, i)
	DdManager*	dd
	DdNode*		f
	int		i
PREINIT:
	DdNode *node;
CODE:
	node = Cudd_Decreasing(dd, f, i);
	RETVAL = node == Cudd_ReadOne(dd);
OUTPUT:
	RETVAL

int
Cudd_Increasing(dd, f, i)
	DdManager*	dd
	DdNode*		f
	int		i
PREINIT:
	DdNode *node;
CODE:
	node = Cudd_Increasing(dd, f, i);
	RETVAL = node == Cudd_ReadOne(dd);
OUTPUT:
	RETVAL

AV*
Cudd_FindEssential(dd, f)
	DdManager*	dd
	DdNode*		f
PREINIT:
	DdNode *zero, *essent, *cube, *scan;
	int complement;
	SV *sv;
CODE:
	cube = Cudd_FindEssential(dd, f);
	Cudd_Ref(cube);
	RETVAL = newAV();
	complement = Cudd_IsComplement(cube);
	scan = Cudd_Regular(cube);

	while (!Cudd_IsConstant(scan)) {
		zero = complement ? Cudd_ReadOne(dd) : Cudd_ReadLogicZero(dd);
		essent = Cudd_bddIthVar(dd, Cudd_NodeReadIndex(scan));
		if (Cudd_T(scan) == zero) {
			essent = Cudd_Not(essent);
			complement ^= Cudd_IsComplement(Cudd_E(scan));
			scan = Cudd_Regular(Cudd_E(scan));
		} else {
			scan = Cudd_T(scan);
		}
		sv = newSViv((IV)0);
		sv_setref_pv(sv, "DdNodePtr", (void*)essent);
		av_push(RETVAL, sv);
	}
	Cudd_RecursiveDeref(dd,cube);
OUTPUT:
	RETVAL
CLEANUP:
	# Decrement refcount from the typemap newAV.
	SvREFCNT_dec(RETVAL);

DdNode *
Cudd_Support(dd, f)
	DdManager*	dd
	DdNode*		f

DdNode *
Cudd_bddLiteralSetIntersection(dd, f, g)
	DdManager*	dd
	DdNode*		f
	DdNode*		g

DdNode *
Cudd_bddSwapVariables(dd, f, x, y)
	DdManager*	dd
	DdNode*		f
PREINIT:
	I32 len;
	I32 index;
	SV  *rvx, *rvy;
	SV  *svx, *svy;
	DdNode  **xvars, **yvars;
CODE:
	rvx = ST(2);
	rvy = ST(3);
	if (!SvROK(rvx) || !SvROK(rvy))
		croak("Not a reference given to SwapVariables");
	svx = SvRV(rvx);
	svy = SvRV(rvy);
	if (SvTYPE(svx) != SVt_PVAV || SvTYPE(svy) != SVt_PVAV)
		croak("Not array reference given to SwapVariables");
	if (av_len((AV*)svx) < 0)
		croak("Empty array reference given to SwapVariables");
	if (av_len((AV*)svx) != av_len((AV*)svy))
		croak("SwapVariables given variable sets of different size");
	len = av_len((AV*)svx) + 1;
	xvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	yvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	for (index = 0; index < len; index++) {
		xvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svx, index, FALSE)));
		yvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svy, index, FALSE)));
	}
	RETVAL = Cudd_bddSwapVariables(dd, f, xvars, yvars, len);
	safefree(xvars);
	safefree(yvars);
OUTPUT:
	RETVAL

DdNode *
Cudd_SubsetHeavyBranch(dd, f, numVars, threshold)
	DdManager*	dd
	DdNode*		f
	int		numVars
	int		threshold

DdNode *
Cudd_SupersetHeavyBranch(dd, f, numVars, threshold)
	DdManager*	dd
	DdNode*		f
	int		numVars
	int		threshold

DdNode *
Cudd_SubsetShortPaths(dd, f, numVars, threshold, hardlimit)
	DdManager*	dd
	DdNode*		f
	int		numVars
	int		threshold
	int		hardlimit

DdNode *
Cudd_SupersetShortPaths(dd, f, numVars, threshold, hardlimit)
	DdManager*	dd
	DdNode*		f
	int		numVars
	int		threshold
	int		hardlimit

DdNode *
Cudd_Not(f)
	DdNode*		f

int
Cudd_ReadPerm(dd, index)
	DdManager*	dd
	int		index

int
Cudd_bddLeq(dd,f,g)
	DdManager*	dd
	DdNode*		f
	DdNode*		g

DdNode *
Cudd_ShortestPath(manager, f, length)
	DdManager*	manager
	DdNode*		f
	int		length
	CODE:
	    RETVAL = Cudd_ShortestPath(manager, f, NULL, NULL, &length);
	OUTPUT:
	length
	RETVAL

void
Cudd_AutodynEnable(unique, method = CUDD_REORDER_SAME)
	DdManager*	unique
	int		method

void
Cudd_AutodynDisable(unique)
	DdManager*	unique

int
Cudd_EnableReorderingReporting(dd)
	DdManager*	dd

int
Cudd_DisableReorderingReporting(dd)
	DdManager*	dd

int
Cudd_ReduceHeap(table, heuristic = CUDD_REORDER_SIFT, minsize = 1)
	DdManager*	table
	int		heuristic
	int		minsize

int
Cudd_ShuffleHeap(table,permutation)
	DdManager*	table
PREINIT:
    I32 len;
    I32 index;
    SV  *rv;
    SV  *sv;
    int  *parray;
CODE:
    rv = ST(1);
    if (!SvROK(rv))
	croak("Not a reference given to Shuffle");
    sv = SvRV(rv);
    if (SvTYPE(sv) != SVt_PVAV)
	croak("Not array reference given to Shuffle");
    if (av_len((AV*)sv) < 0)
	croak("Empty array reference given to Shuffle");
    len = av_len((AV*)sv) + 1;
    if (len != Cudd_ReadSize(table))
	croak("Wrong number of variables");
    parray = (int *) safemalloc(len * sizeof(int));
    for (index = 0; index < len; index++) {
	parray[index] = SvIV(*av_fetch((AV*)sv, index, FALSE));
    }
    RETVAL = Cudd_ShuffleHeap(table,parray);
    safefree(parray);
OUTPUT:
    RETVAL


int
Cudd_ReadSize(dd)
	DdManager*	dd

int
Cudd_NodeReadIndex(node)
	DdNode*		node

int
Cudd_IsComplement(node)
	DdNode*		node

int
Cudd_CheckZeroRef(manager)
	DdManager*	manager

int
Cudd_DumpDot(dd,f,onameref,inameref)
	DdManager *dd
PREINIT:
	I32 leno, leni;
	I32 index;
	SV  *rvf, *rvo, *rvi;
	SV  *svf, *svo, *svi;
	DdNode  **fa;
	char **onames, **inames;
CODE:
	/* Process list of output nodes. */
	rvf = ST(1);
	if (!SvROK(rvf))
		croak("Not a reference given to Dot");
	svf = SvRV(rvf);
	if (SvTYPE(svf) != SVt_PVAV)
		croak("Not array reference given to Dot");
	if (av_len((AV*)svf) < 0)
		croak("Empty array reference given to Dot");
	leno = av_len((AV*)svf) + 1;
	fa = (DdNode **) safemalloc(leno * sizeof(DdNode *));
	for (index = 0; index < leno; index++) {
		fa[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svf, index, FALSE)));
	}
	/* Process list of output names. */
	rvo = ST(2);
	if (!SvROK(rvo))
		croak("Not a reference given to Dot");
	svo = SvRV(rvo);
	if (SvTYPE(svo) != SVt_PVAV)
		croak("Not array reference given to Dot");
	if (av_len((AV*)svo) < 0) {
		onames = NULL;
	} else {
		if (leno != av_len((AV*)svo) + 1)
			croak("Number of output names is incorrect in Dot");
		onames = (char **) safemalloc(leno * sizeof(char *));
		for (index = 0; index < leno; index++) {
			onames[index] =
				SvPV(*av_fetch((AV*)svo, index, FALSE), PL_na);
		}
	}
	/* Process list of input names. */
	rvi = ST(3);
	if (!SvROK(rvi))
		croak("Not a reference given to Dot");
	svi = SvRV(rvi);
	if (SvTYPE(svi) != SVt_PVAV)
		croak("Not array reference given to Dot");
	if (av_len((AV*)svi) < 0) {
		inames = NULL;
	} else {
		leni = av_len((AV*)svi) + 1;
		if (leni != Cudd_ReadSize(dd))
			croak("Number of input names is incorrect in Dot");
		inames = (char **) safemalloc(leni * sizeof(char *));
		for (index = 0; index < leni; index++) {
			inames[index] =
				SvPV(*av_fetch((AV*)svi, index, FALSE), PL_na);
		}
	}
	RETVAL = Cudd_DumpDot(dd, leno, fa, inames, onames, stdout);
	safefree(fa);
	if (onames != NULL) safefree(onames);
	if (inames != NULL) safefree(inames);
OUTPUT:
	RETVAL

void
Cudd_SolveEqn(dd, F, Y, n)
	DdManager*	dd
	DdNode*		F
	DdNode*		Y
	int		n
PREINIT:
	DdNode *consist;
	I32 index;
	AV *pG;
	DdNode **G;
	int *yIndex;
	SV *sv;
PPCODE:
	G = (DdNode **) safemalloc(n * sizeof(DdNode *));
	consist = Cudd_SolveEqn(dd, F, Y, G, &yIndex, n);
	pG = newAV();
	for (index = 0; index < n; index++) {
		sv = newSViv((IV)0);
		sv_setref_pv(sv, "DdNodePtr", (void*)G[index]);
		av_push(pG, sv);
	}
	safefree(G);
	FREE(yIndex);
	EXTEND(sp,2);
	sv = newSViv((IV)0);
	PUSHs(sv_2mortal(sv_setref_pv(sv, "DdNodePtr", (void*)consist)));
	PUSHs(sv_2mortal(newRV((SV*)pG)));

AV*
Cudd_CofMinterm(dd, node)
	DdManager*	dd
	DdNode*		node
PREINIT:
	int n;
	I32 index;
	double *signatures;
	SV *sv;
CODE:
	n = Cudd_ReadSize(dd);
	signatures = Cudd_CofMinterm(dd, node);
	RETVAL = newAV();
	for (index = 0; index <= n; index++) {
		sv = newSVnv(signatures[index]);
		av_push(RETVAL, sv);
	}
	FREE(signatures);
OUTPUT:
	RETVAL
CLEANUP:
	# Decrement refcount from the typemap's newAV.
	SvREFCNT_dec(RETVAL);

void
Cudd_ReorderingStatus(dd)
	DdManager*	dd
PREINIT:
	Cudd_ReorderingType method;
	int enabled;
PPCODE:
	enabled = Cudd_ReorderingStatus(dd, &method);
	EXTEND(sp, 2);
	PUSHs(sv_2mortal(newSViv(enabled)));
	PUSHs(sv_2mortal(newSViv(method)));

DdNode *
Cudd_bddIntersect(dd, f, g)
	DdManager*	dd
	DdNode*		f
	DdNode*		g

AV*
Cudd_bddConstrainDecomp(dd, f)
	DdManager*	dd
	DdNode*		f
PREINIT:
	DdNode **array;
	int i, nvars;
	SV *sv;
CODE:
	array = Cudd_bddConstrainDecomp(dd, f);
	RETVAL = newAV();
	nvars = Cudd_ReadSize(dd);
	for (i = 0; i < nvars; i++) {
		sv = newSViv((IV)0);
		sv_setref_pv(sv, "DdNodePtr", (void*)array[i]);
		av_push(RETVAL, sv);
	}
	FREE(array);
OUTPUT:
	RETVAL
CLEANUP:
	# Decrement refcount from the typemap's newAV.
	SvREFCNT_dec(RETVAL);

AV*
Cudd_bddCharToVect(dd, f)
	DdManager*	dd
	DdNode*		f
PREINIT:
	DdNode **array;
	int i, nvars;
	SV *sv;
CODE:
	array = Cudd_bddCharToVect(dd, f);
	RETVAL = newAV();
	nvars = Cudd_ReadSize(dd);
	for (i = 0; i < nvars; i++) {
		sv = newSViv((IV)0);
		sv_setref_pv(sv, "DdNodePtr", (void*)array[i]);
		av_push(RETVAL, sv);
	}
	FREE(array);
OUTPUT:
	RETVAL
CLEANUP:
	# Decrement refcount from the typemap's newAV.
	SvREFCNT_dec(RETVAL);

DdNode *
Cudd_PrioritySelect(dd, R, Pi, xvarref, yvarref, zvarref)
	DdManager*	dd
	DdNode*		R
	DdNode*		Pi
PREINIT:
	I32 len;
	I32 index;
	SV  *rvx, *rvy, *rvz;
	SV  *svx, *svy, *svz;
	DdNode  **xvars, **yvars, **zvars;
CODE:
	rvx = ST(3);
	rvy = ST(4);
	rvz = ST(5);
	if (!SvROK(rvx) || !SvROK(rvy) || !SvROK(rvz))
		croak("Not a reference given to PrioritySelect");
	svx = SvRV(rvx);
	svy = SvRV(rvy);
	svz = SvRV(rvz);
	if (SvTYPE(svx) != SVt_PVAV || SvTYPE(svy) != SVt_PVAV ||
	    SvTYPE(svz) != SVt_PVAV)
		croak("Not array reference given to PrioritySelect");
	if (av_len((AV*)svx) < 0)
		croak("Empty array reference given to PrioritySelect");
	if (av_len((AV*)svx) != av_len((AV*)svy) ||
	    av_len((AV*)svx) != av_len((AV*)svz))
		croak("PrioritySelect given variable sets of different size");
	len = av_len((AV*)svx) + 1;
	xvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	yvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	zvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	for (index = 0; index < len; index++) {
		xvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svx, index, FALSE)));
		yvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svy, index, FALSE)));
		zvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svz, index, FALSE)));
	}
	RETVAL = Cudd_PrioritySelect(dd, R, xvars, yvars, zvars, Pi,
				     len, NULL);
	safefree(xvars);
	safefree(yvars);
	safefree(zvars);
OUTPUT:
	RETVAL

DdNode *
Cudd_Dxygtdxz(dd, xvarref, yvarref, zvarref)
	DdManager*	dd
PREINIT:
	I32 len;
	I32 index;
	SV  *rvx, *rvy, *rvz;
	SV  *svx, *svy, *svz;
	DdNode  **xvars, **yvars, **zvars;
CODE:
	rvx = ST(1);
	rvy = ST(2);
	rvz = ST(3);
	if (!SvROK(rvx) || !SvROK(rvy) || !SvROK(rvz))
		croak("Not a reference given to Dxygtdxz");
	svx = SvRV(rvx);
	svy = SvRV(rvy);
	svz = SvRV(rvz);
	if (SvTYPE(svx) != SVt_PVAV || SvTYPE(svy) != SVt_PVAV ||
	    SvTYPE(svz) != SVt_PVAV)
		croak("Not array reference given to Dxygtdxz");
	if (av_len((AV*)svx) < 0)
		croak("Empty array reference given to Dxygtdxz");
	if (av_len((AV*)svx) != av_len((AV*)svy) ||
	    av_len((AV*)svx) != av_len((AV*)svz))
		croak("Dxygtdxz given variable sets of different size");
	len = av_len((AV*)svx) + 1;
	xvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	yvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	zvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	for (index = 0; index < len; index++) {
		xvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svx, index, FALSE)));
		yvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svy, index, FALSE)));
		zvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svz, index, FALSE)));
	}
	RETVAL = Cudd_Dxygtdxz(dd, len, xvars, yvars, zvars);
	safefree(xvars);
	safefree(yvars);
	safefree(zvars);
OUTPUT:
	RETVAL

DdNode *
Cudd_Dxygtdyz(dd, xvarref, yvarref, zvarref)
	DdManager*	dd
PREINIT:
	I32 len;
	I32 index;
	SV  *rvx, *rvy, *rvz;
	SV  *svx, *svy, *svz;
	DdNode  **xvars, **yvars, **zvars;
CODE:
	rvx = ST(1);
	rvy = ST(2);
	rvz = ST(3);
	if (!SvROK(rvx) || !SvROK(rvy) || !SvROK(rvz))
		croak("Not a reference given to Dxygtdyz");
	svx = SvRV(rvx);
	svy = SvRV(rvy);
	svz = SvRV(rvz);
	if (SvTYPE(svx) != SVt_PVAV || SvTYPE(svy) != SVt_PVAV ||
	    SvTYPE(svz) != SVt_PVAV)
		croak("Not array reference given to Dxygtdyz");
	if (av_len((AV*)svx) < 0)
		croak("Empty array reference given to Dxygtdyz");
	if (av_len((AV*)svx) != av_len((AV*)svy) ||
	    av_len((AV*)svx) != av_len((AV*)svz))
		croak("Dxygtdyz given variable sets of different size");
	len = av_len((AV*)svx) + 1;
	xvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	yvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	zvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	for (index = 0; index < len; index++) {
		xvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svx, index, FALSE)));
		yvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svy, index, FALSE)));
		zvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svz, index, FALSE)));
	}
	RETVAL = Cudd_Dxygtdyz(dd, len, xvars, yvars, zvars);
	safefree(xvars);
	safefree(yvars);
	safefree(zvars);
OUTPUT:
	RETVAL

DdNode *
Cudd_Xgty(dd, zvarref, xvarref, yvarref)
	DdManager*	dd
PREINIT:
	I32 len;
	I32 index;
	SV  *rvx, *rvy, *rvz;
	SV  *svx, *svy, *svz;
	DdNode  **xvars, **yvars, **zvars;
CODE:
	rvz = ST(1);
	rvx = ST(2);
	rvy = ST(3);
	if (!SvROK(rvx) || !SvROK(rvy) || !SvROK(rvz))
		croak("Not a reference given to Xgty");
	svz = SvRV(rvz);
	svx = SvRV(rvx);
	svy = SvRV(rvy);
	if (SvTYPE(svx) != SVt_PVAV || SvTYPE(svy) != SVt_PVAV ||
	    SvTYPE(svz) != SVt_PVAV)
		croak("Not array reference given to Xgty");
	if (av_len((AV*)svx) < 0)
		croak("Empty array reference given to Xgty");
	if (av_len((AV*)svx) != av_len((AV*)svy))
		croak("Xgty given variable sets of different size");
	len = av_len((AV*)svx) + 1;
	xvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	yvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	zvars = (DdNode **) safemalloc(len * sizeof(DdNode *));
	for (index = 0; index < len; index++) {
		xvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svx, index, FALSE)));
		yvars[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svy, index, FALSE)));
	}
	RETVAL = Cudd_Xgty(dd, len, zvars, xvars, yvars);
	safefree(xvars);
	safefree(yvars);
	safefree(zvars);
OUTPUT:
	RETVAL

DdNode *
Cudd_CProjection(manager, R, Y)
	DdManager*	manager
	DdNode*		R
	DdNode*		Y

int
Cudd_SharingSize(ddref)
PREINIT:
	I32 len;
	I32 index;
	SV  *rvx;
	SV  *svx;
	DdNode  **dds;
CODE:
	rvx = ST(0);
	if (!SvROK(rvx))
		croak("Not a reference given to Size");
	svx = SvRV(rvx);
	if (SvTYPE(svx) != SVt_PVAV)
		croak("Not array reference given to Size");
	if (av_len((AV*)svx) < 0)
		croak("Empty array reference given to Size");
	len = av_len((AV*)svx) + 1;
	dds = (DdNode **) safemalloc(len * sizeof(DdNode *));
	for (index = 0; index < len; index++) {
		dds[index] = (DdNode *)
			SvIV(SvRV(*av_fetch((AV*)svx, index, FALSE)));
	}
	RETVAL = Cudd_SharingSize(dds, len);
	safefree(dds);
OUTPUT:
	RETVAL
