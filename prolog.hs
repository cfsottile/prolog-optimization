module Prolog
    ( compileAndAskIf
    , compileAndAskAll
    , askIf
    , askAll
    , genMap
    , isGround
    ) where

import qualified Data.Map as Map
import qualified Data.List as List
import Data.Maybe

import Datatypes

--------------------------------------------------------------------------------
-- Interface                                                                  --
--------------------------------------------------------------------------------

compileAndAskIf :: Term -> Program -> Bool
compileAndAskIf t = askIf t . genMap

compileAndAskAll :: Term -> Program -> [Substitution]
compileAndAskAll t p = askAll t (genMap p)

askIf :: Term -> ProgramMap -> Bool
askIf t = not . null . askAll t

--------------------------------------------------------------------------------
-- PrologContext                                                              --
--------------------------------------------------------------------------------

data PrologContext = PC Substitution Int deriving (Eq,Show)

-- getFreshVariable :: State PrologContext Term
-- getFreshVariable = state $ \(PC sub fresh) -> (Var $ "FVAR" ++ show fresh, PC sub (fresh+1))
getFreshVariable :: PrologContext -> (Term,PrologContext)
getFreshVariable (PC sub fresh) = (Var $ "FVAR" ++ show fresh, PC sub (fresh+1))

-- setSub :: Substitution -> State PrologContext ()
-- setSub sub = state $ \(PC _ fresh) -> ((), PC sub fresh)
setSub :: PrologContext -> Substitution -> PrologContext
setSub (PC _ fresh) sub = PC sub fresh

getSub :: PrologContext -> Substitution
getSub (PC sub _) = sub

inSub :: Term -> Substitution -> Bool
inSub t sub = Map.member t sub

inSubPC :: Term -> PrologContext -> Bool
inSubPC t (PC sub _) = inSub t sub

addSubPC :: Term -> Term -> PrologContext -> PrologContext
addSubPC v t (PC sub fresh) = PC (Map.insert v t sub) fresh

--------------------------------------------------------------------------------
-- "Compiling"                                                                --
--------------------------------------------------------------------------------

genMap :: Program -> ProgramMap
genMap program = foldr genKeyValuePair Map.empty (nameClauses program)
    where
        nameUnifiers name = filter (nameUnify name) program
        genKeyValuePair name programMap =
            Map.insert name (nameUnifiers name) programMap

nameUnify :: Name -> Clause -> Bool
nameUnify name1 (Rule (Pred name2 _) _) = name1 == name2
nameUnify _ _ = False

-- | Reduces the program to a list of the Names of its Clauses.
nameClauses :: Program -> [Name]
nameClauses program = List.nub $ mapMaybe getName program

getName :: Clause -> Maybe Name
getName (Rule (Pred name _) _) = Just name
getName _ = Nothing

--------------------------------------------------------------------------------
-- Proof search                                                               --
--------------------------------------------------------------------------------

askAll :: Term -> ProgramMap -> [Substitution]
askAll t pm =
    let vs = variables t
        pcs = ask t pm (PC Map.empty 1)
        subs = getSub <$> pcs
        results = Map.filterWithKey (\v _ -> elem v vs) <$> subs
    in  zipWith (\sub res -> Map.mapWithKey (\k _ -> unfold' sub k) res) subs results

variables :: Term -> [Term]
variables v@(Var _) = [v]
variables (Pred name args) = List.nub $ concat $ variables <$> args

isGround :: Term -> Bool
isGround (Var _) = False
isGround (Pred name args) = all isGround args

ask :: Term -> ProgramMap -> PrologContext -> [PrologContext]
ask p@(Pred name _) pm pc = 
    let mayUnifyClauses = concat $ Map.lookup name pm
        mayUnifyFreshClauses = map (freshClause pc) mayUnifyClauses
        unifyingClausesGoals = mapMaybe (\(c,pc') -> unify p pc' c) mayUnifyFreshClauses
        explore' (goals,pc) = explore goals pm pc
    in  concat $ explore' <$> unifyingClausesGoals

explore :: Goals -> ProgramMap -> PrologContext -> [PrologContext]
explore [] _ pc = [pc]
explore (g:gs) pm pc = ask g pm pc >>= explore gs pm

unify :: Term -> PrologContext -> Clause -> Maybe (Goals,PrologContext)
unify t1 pc (Rule pred goals) = (,) goals <$> unify' t1 pred pc

freshClause :: PrologContext -> Clause -> (Clause,PrologContext)
freshClause pc (Rule head goals) =
    let (head', lsub, pc') = freshTerm head pc Map.empty
        (goals', lsub', pc'') = freshGoals goals pc' lsub
    in (Rule head' goals', pc'')

freshGoals :: Goals -> PrologContext -> Substitution -> (Goals,Substitution,PrologContext)
freshGoals [] pc lsub = ([],lsub,pc)
freshGoals (g:gs) pc lsub =
    let (g', lsub', pc') = freshTerm g pc lsub
        (gs', lsub'', pc'') = freshGoals gs pc' lsub'
    in  (g':gs', lsub'', pc'')

freshTerm :: Term -> PrologContext -> Substitution -> (Term,Substitution,PrologContext)
freshTerm v@(Var _) pc lsub
    | v `inSub` lsub = (fromJust $ Map.lookup v lsub, lsub, pc)
    | otherwise =
        let (v',pc') = getFreshVariable pc
        in  (v', Map.insert v v' lsub, pc')
freshTerm (Pred name args) pc lsub =
    let (args', lsub', pc') = freshArgs args pc lsub
    in  (Pred name args', lsub', pc')

freshArgs = freshGoals

unfold :: PrologContext -> Term -> Term
unfold pc = unfold' (getSub pc)

unfold' :: Substitution -> Term -> Term
unfold' sub v@(Var _) =
    let t = fromMaybe v (Map.lookup v sub)
    in  if t == v then v
                  else unfold' sub t
unfold' sub (Pred name args) = Pred name (unfold' sub <$> args)

-- las variables de t2 son fresh
unify' :: Term -> Term -> PrologContext -> Maybe PrologContext
unify' v1@(Var _) v2@(Var _) pc
    |      v1 `inSubPC` pc  &&      v2 `inSubPC` pc  = unify' (unfold pc v1) (unfold pc v2) pc
    |      v1 `inSubPC` pc  && not (v2 `inSubPC` pc) = Just $ addSubPC v2 (unfold pc v1) pc
    | not (v1 `inSubPC` pc) &&      v2 `inSubPC` pc  = Just $ addSubPC v1 (unfold pc v2) pc
    | not (v1 `inSubPC` pc) && not (v2 `inSubPC` pc) = Just $ addSubPC v1 v2 pc

unify' v@(Var _) t pc = Just $ addSubPC v (unfold pc t) pc

unify' t v@(Var _) pc
    -- acá quizá debería meterse una fresh var en reemplazo de v
    | not (v `inSubPC` pc) = Just $ addSubPC v (unfold pc t) pc
        -- let (v',pc') = getFreshVariable pc
        --     pc'' = addSubPC v v'
        -- in  Just $ addSubPC v' (unfold t pc'') pc''
    | otherwise = unify' (unfold pc t) (unfold pc v) pc

unify' (Pred name1 args1) (Pred name2 args2) val
    | name1 == name2 && length args1 == length args2 = argsUnify args1 args2 val
    | otherwise = Nothing

-- unify _ _ _ = Nothing

argsUnify :: [Term] -> [Term] -> PrologContext -> Maybe PrologContext
argsUnify [] [] pc = Just pc
argsUnify (a1:as1) (a2:as2) pc =
    unify' (unfold pc a1) (unfold pc a2) pc >>= argsUnify as1 as2