{-# OPTIONS -fglasgow-exts #-}

module PolyLib.FunctorOf (deriveFunctorOf) where

import Control.Monad.Error
import Data.Char
import Data.List
import Language.Haskell.THSyntax

type ConName	= String
type TypeName	= String
type VarName	= String

data Code   = Code :+: Code
	    | Code :*: Code
	    | Unit
	    | Par
	    | Rec
	    | Regular :@: Code
	    | Code :->: Code
	    | Const Type

type Regular	= (TypeName, [ConName], Code)

type ErrM = Either String

-- Deriving FunctorOf -----------------------------------------------------

deriveFunctorOf :: Q Dec -> Q [Dec]
deriveFunctorOf q =
    do	dec <- q
	functorOf (regular [dec] $ declaredName dec)

-- Regular ----------------------------------------------------------------

regular :: [Dec] -> TypeName -> Regular
regular ds name = either error id $ env name >>= mkRegular 
    where
	env = mkDecEnv ds

	mkRegular :: Dec -> ErrM Regular
	mkRegular d = case d of

		DataD _ _ [a] cons _	->
		    do	code <- mkSum a cons
			return (name, map conName cons, code)

		NewtypeD _ _ [a] con _	->
		    do	code <- mkProd a con
			return (name, [conName con], code)

		_			-> notRegular
	    where

		myName = declaredName d

		notRegular	= fail $ "regular: Not a regular datatype:\n" ++ show (pprDec d)
		undefinedVar x	= fail $ "regular: Undefined type variable " ++ x ++ " in\n" ++ show (pprDec d)

		mkSum :: VarName -> [Con] -> ErrM Code
		mkSum arg []	= notRegular
		mkSum arg cons	= liftM (foldr1 (:+:)) $ mapM (mkProd arg) cons

		mkProd :: VarName -> Con -> ErrM Code
		mkProd arg con   = liftM foldProd
				    $ mapM (mkType arg)
				    $ constructorArguments con
		    where
			foldProd [] = Unit
			foldProd cs = foldr1 (:*:) cs

		mkType :: VarName -> Type -> ErrM Code
		mkType arg t = foldr1 mplus

		    [	-- Is it a variable?
			do  x <- varName t
			    if arg == x
				then return Par
				else undefinedVar x

		    ,	-- Is it an application?
			case t of
			    -- Maybe it's a function space
			    ArrowT `AppT` t1 `AppT` t2 ->
				do  f <- mkType arg t1
				    g <- mkType arg t2
				    return $ f :->: g
			    AppT t1 t2  ->
				do  name <- typeName t1

				    -- Is it a recursive call?
				    if name == myName
					-- then it should be a Rec
					then do a <- varName t2
						if a == arg
						    then return Rec
						    else notRegular
					-- else it might be a (:@:)
					else do d   <- env name
						r   <- mkRegular d
						c   <- mkType arg t2
						return $ r :@: c

		    ,	-- Otherwise it better be closed
			if isClosed t
			    then return $ Const t
			    else notRegular
		    ]

-- From Structure Types to Datatypes --------------------------------------

constructorArities :: Regular -> [(ConName, Int)]
constructorArities d = case d of
	(_, con:[], c)		-> [(con, arity c)]
	(name, con:cons, c :+: c')	->
	    (con, arity c) : constructorArities (name, cons, c')
    where
	arity Unit	= 0
	arity (_ :*: c) = 1 + arity c
	arity _		= 1

-- FunctorOf --------------------------------------------------------------

patternFunctorType :: Code -> TypeQ
patternFunctorType = pft
    where
	pft (g :+: h)	= conT "SumF" `appT` pft g `appT` pft h
	pft (g :*: h)	= conT "ProdF" `appT` pft g `appT` pft h
	pft Unit	= conT "EmptyF"
	pft Par		= conT "ParF"
	pft Rec		= conT "RecF"
	pft (Const t)	= conT "ConstF" `appT` (return t)
	pft (d :@: g)	= conT (pi1_3 d) `appT` pft g
	pft (f :->: g)	= conT "FunF" `appT` pft f `appT` pft g

functorOf :: Regular -> Q [Dec]
functorOf d@(name, cons, pf) = sequence
	[ instanceD (cxt [])
		    (conT "FunctorOf" `appT` patternFunctorType pf `appT` conT name)
		    [ funD "inn" innDef
		    , funD "out" outDef
 		    , funD "constructorName" conNameDef
-- 		    , funD "constructorFixity" conFixDef
 		    , funD "datatypeName" dataNameDef
		    ]
	]
    where
	constructors = constructorArities d
	nofCons	= length $ cons

	innDef = matches
	    where
		matches = zipWith mkMatch [0..] constructors

		leftAndRights 0 1 p = p
		leftAndRights 0 n p = conP "PolyLib.Prelude:InL" [p]
		leftAndRights i n p = conP "PolyLib.Prelude:InR" [leftAndRights (i-1) (n-1) p]

		tupleP []   = conP "PolyLib.Prelude:EmptyF" []
		tupleP ps   = foldr1 (\x y -> conP "PolyLib.Prelude::*:" [x,y]) ps

		mkMatch i (name, ar) =
		    do	xs <- replicateM ar (gensym "x")
			clause [pat xs] (normalB $ body xs) []
		    where
			pat xs	= leftAndRights i nofCons (tupleP $ map varP xs)
			body xs	= foldl appE (conE name) $ map (\x -> varE "PolyLib.Prelude:from" `appE` varE x) xs

	outDef = matches
	    where
		matches = zipWith mkMatch [0..] constructors

		leftAndRights 0 1 e = e
		leftAndRights 0 n e = conE "PolyLib.Prelude:InL" `appE` e
		leftAndRights i n e = conE "PolyLib.Prelude:InR" `appE` leftAndRights (i-1) (n-1) e

		tupleE []   = conE "PolyLib.Prelude:EmptyF"
		tupleE es   = foldr1 (\x y -> conE "PolyLib.Prelude::*:" `appE` x `appE` y) es

		mkMatch i (name, ar) =
		    do	xs <- replicateM ar (gensym "x")
			clause [pat xs] (normalB $ body xs) []
		    where
			pat xs	= conP name $ map varP xs
			body xs	= leftAndRights i nofCons (tupleE $ map (\x -> varE "PolyLib.Prelude:to" `appE` varE x) xs)

	conNameDef = map mkClause constructors
	    where
		mkClause (name, ar) = clause [pat] (normalB body) []
		    where
			pat	= conP name $ replicate ar wildP
			body	= litE $ stringL name
	conFixDef = []
	dataNameDef = [ clause [wildP] (normalB $ litE $ stringL name) [] ]

---------------------------------------------------------------------------
-- Template Haskell helpers -----------------------------------------------
---------------------------------------------------------------------------

-- Declaration environments -----------------------------------------------

type DecEnv = String -> Either String Dec

mkDecEnv :: [Dec] -> DecEnv
mkDecEnv ds = \name -> maybe	(fail $ "lookupDec: Nothing known about " ++ name)
				return
				(lookup name env)
    where
	env = map (declaredName /\ id) ds

lookupDec = ($)

-- Constructors -----------------------------------------------------------

constructorArguments :: Con -> [Type]
constructorArguments (NormalC _ ts)	= map snd ts
constructorArguments (RecC _ vts)	= map pi3_3 vts
constructorArguments (InfixC t1 _ t2)	= map snd [t1,t2]

-- Names ------------------------------------------------------------------

varName :: Type -> ErrM String
varName (VarT x)    = return x
varName (ConT x)
    | isVar x	    = return x
varName t	    = fail $ "varName: Not a variable " ++ show t

typeName :: Type -> ErrM String
typeName (VarT x)
    | not (isVar x) = return x
typeName (ConT c)   = return c
typeName ListT	    = return "GHC.Base:[]"
typeName (TupleT 0) = return "GHC.Base:()"
typeName (TupleT n) = return $ "GHC.Base:(" ++ replicate (n-1) ',' ++ ")"
typeName t	    = fail $ "typeName: Doesn't have a name " ++ show t

isClosed :: Type -> Bool
isClosed = null . freeVars

declaredName :: Dec -> String
declaredName (FunD s _)		    = s
declaredName (DataD _ s _ _ _)	    = s
declaredName (NewtypeD _ s _ _ _)   = s
declaredName (TySynD s _ _)	    = s
declaredName (ClassD _ s _ _)	    = s
declaredName (SigD s _)		    = s
declaredName d			    =
    error $ "declaredName: Don't know how to handle " ++ show d

conName :: Con -> String
conName (NormalC s _)	= s
conName (RecC s _)	= s
conName (InfixC _ s _)	= s

isVar :: String -> Bool
isVar = isLower . head

freeVars :: Type -> [String]
freeVars (VarT x)	    = [x]
freeVars (ConT x) | isVar x = [x]
freeVars (AppT t1 t2)	    = freeVars t1 `union` freeVars t2
freeVars (ForallT xs _ t)   = freeVars t \\ xs
freeVars _		    = []

-- Sums and products ------------------------------------------------------

infix 7 /\
(/\) :: (a -> b) -> (a -> c) -> a -> (b,c)
(f /\ g) x = (f x, g x)

pi1_3 (x,_,_) = x
pi2_3 (_,x,_) = x
pi3_3 (_,_,x) = x

pi12_3 (x,y,_)	= (x,y)
pi13_3 (x,_,y)	= (x,y)
pi23_3 (_,x,y)	= (x,y)

