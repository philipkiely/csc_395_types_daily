{-# LANGUAGE GADTs #-}

module Types where

--------------------------------------------------------------------------------
-- CSC 395 (Spring 2020): Type Systems
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Review: Compilation and Interpretation
--------------------------------------------------------------------------------

-- Previously, we learned that we can think of the compilation pipeline as a
-- series of transformations of a program from one representation to another.
-- One of the most important of these representations is the *abstract syntax
-- tree* (AST) which captures the essential structure of a program.
--
-- We saw how Haskell allows us to coincisely represent an AST using an
-- algebraic data type.  For example, consider the following expression language
-- of integers and booleans:
--
--   e ::= n | b | e1 + e2 | e1 == e2 | if e1 then e2 else e3
--
-- Our expression datatype captures the various alternatives of what an
-- expression could be:

data Exp where
  EInt  :: Int -> Exp                   -- n (an integer literal)
  EBool :: Bool -> Exp                  -- true or false
  EPlus :: Exp -> Exp -> Exp            -- e1 + e2
  EEq   :: Exp -> Exp -> Exp            -- e1 == e2
  EIf   :: Exp -> Exp -> Exp -> Exp     -- if e1 then e2 else e3
  EPair :: Exp -> Exp -> Exp            -- (e1, e2)
  EFst   :: Exp -> Exp                  -- fst e
  ESnd   :: Exp -> Exp                  -- snd e
  deriving (Show, Eq)

e1 = EPlus (EInt 1) (EPlus (EInt 2) (EInt 3))         -- 1 + (2 + 3)
e2 = EIf (EEq (EInt 5) (EInt 2)) (EInt 0) (EInt 1)    -- if 5 == 2 then 0 else 1
e3 = EPair (EInt 1) (EInt 2) -- (1, 2)
e4 = EFst e3                 -- 1
e5 = ESnd e3                 -- 2

-- One kind of "analysis" we can perform on an AST is evaluation, i.e.,
-- actually running the program.  To do this, we needed to differentiate
-- between when the resulting program produced an integers versus a boolean by
-- introducing a value datatype (a value is an expression that takes no further
-- steps of evaluation).

data Val where
  VInt  :: Int -> Val
  VBool :: Bool -> Val
  VPair :: Val -> Val -> Val
  deriving (Show, Eq)

-- With the value datatype, we can define evaluation in a straightforward,
-- recursive manner.  We signal erroneous cases with the Maybe datatype and use
-- monadic syntax to make the resulting code as clean as possible.

eval :: Exp -> Maybe Val
eval (EInt n)      = pure (VInt n)   -- N.B. recall that `pure` is `Just` for Maybe!
eval (EBool b)     = pure (VBool b)
eval (EPlus e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
    (VInt n1, VInt n2) -> pure (VInt $ n1 + n2)
    _                  -> Nothing
eval (EEq e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
    (VInt n1, VInt n2)   -> pure (VBool $ n1 == n2)
    (VBool b1, VBool b2) -> pure (VBool $ b1 == b2)
    _                    -> Nothing
eval (EIf e1 e2 e3) = do
  v1 <- eval e1
  case v1 of
    VBool True  -> eval e2
    VBool False -> eval e3
    _           -> Nothing
eval (EPair e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
    (v1, v2)     -> pure (VPair v1 v2)
eval (EFst e1) = do
   v1 <- eval e1
   case (v1) of
      (VPair (VInt n1) _)     -> pure (VInt n1)
      (VPair (VBool b1) _)    -> pure (VBool b1)
      (VPair (VPair p1 p2) _) -> pure (VPair p1 p2)
      _                -> Nothing
eval (ESnd e2) = do
   v2 <- eval e2
   case (v2) of
      (VPair _ (VInt n2))     -> pure (VInt n2)
      (VPair _ (VBool b2))    -> pure (VBool b2)
      (VPair _ (VPair p1 p2)) -> pure (VPair p1 p2)
      _                -> Nothing 

v1 = eval e1    -- Just (VInt 6)
v2 = eval e2    -- Just (VInt 1)
v3 = eval e3    -- Just (VPair 1 2)
v4 = eval e4    -- Just (VInt 1)
v5 = eval e5    -- Just (VInt 2)

--------------------------------------------------------------------------------
-- Type Systems
--------------------------------------------------------------------------------

-- We noted that the introduction of booleans into the language opened up the
-- possibility of users entering invalid programs!  For example, the program
--
--   1 + True
--
-- Leads to an error (`Nothing` in our eval function).
--
-- We can add a pass to our compiler to check for these erroneous usages of
-- operators, called a *type checking pass*.  Type checking relies on a *type
-- system* which specifies the legal ways we can use operators in our program.

-- A type system consists of a grammar of types that we add to the language.  The
-- grammar of types for this language is very straightforward:
--
--   t ::= int | bool

-- There are two types in the language---integers and booleans.  We can declare a
-- corresponding algebraic data type to represents types in our type checker:

data Typ where    -- N.B. Type is a keyword... >_<
  TInt  :: Typ
  TBool :: Typ
  TPair :: Typ
  deriving (Eq, Show)

-- In addition to our grammar of types, we also specify a *deductive framework*
-- relating well-typed expressions to their types.  Traditionally, we specify
-- this framework with a collection of *inference rules* defining what it means
-- for expressions to be well-typed.  (This notation should be familiar to
-- anyone that has taken a logic class!)

-- First, let's define a relation "e : t" stating that expression e has type t.
-- Then we can define when we are allowed to conclude an expression has a
-- particular type by case analysis on the shape of e.  For example, here is
-- the rule for integer literals:

--
--    --------- :: t-int
--     n : int
--
-- (We'll use `n` to represent an arbitrary integer literal).  An inference
-- rule is composed of two parts.  Below the line is the *conclusion* of the
-- rule which is what we are allowed to assume provided that the conditions
-- above the line hold, *i.e.*, the rule's *premises*.  This particular rule,
-- t-int, says that we consider any integer literal to be of type int without
-- any premises.  We call such a rule an `axiom` in our system.
--
-- Here is an example of the typing rule for addition:
--
--    e1 : int    e2 : int
--    -------------------- :: t-add
--       e1 + e2 : int
--
-- This rule states that an addition is well-typed at type int whenever its two
-- operands also are well-typed at type int.
--
-- In contrast, here is a rule for the equals operator:
--
--    e1 : int    e2 : int
--    -------------------- :: t-bool-int
--       e1 == e2 : bool
--
-- Which is like addition except that we conclude that the less-than operation
-- produces a boolean rather than an integer.  Note that we could also compare
-- booleans together, so here is another rule that acts similarly but for
-- booleans:
--
--    e1 : bool   e2 : bool
--    --------------------- :: t-bool-bool
--       e1 == e2 : bool
--
-- Combined, these two rules allow us to typecheck an equality as long as its
-- sub-expressions are both of the same type.
--
-- The typing rules for the other operators follow similarly from these, so we
-- won't replicate them here.  (It's a good exercise to write down the full
-- type system on your own!)  From these rules, we can implement our type
-- checking pass.  To do so, we can think of the conclusion as the case that
-- we are considering and the premises above the line as our instructions
-- for checking that case.

-- typecheck e returns the deduced type of e if it is well-typed.
typecheck :: Exp -> Maybe Typ
typecheck (EInt _)      = pure TInt
typecheck (EBool _)     = pure TBool
typecheck (EPlus e1 e2) = do
  t1 <- typecheck e1
  t2 <- typecheck e2
  case (t1, t2) of
    (TInt, TInt) -> pure TInt
    _            -> Nothing
typecheck (EEq e1 e2) = do
  t1 <- typecheck e1
  t2 <- typecheck e2
  case (t1, t2) of
    (TInt, TInt)   -> pure TBool
    (TBool, TBool) -> pure TBool
    _              -> Nothing
typecheck (EIf e1 e2 e3) = do
  t1 <- typecheck e1
  t2 <- typecheck e2
  t3 <- typecheck e3
  case (t1, t2, t3) of
    (TBool, TInt, TInt)   -> pure TInt
    (TBool, TBool, TBool) -> pure TBool
    _              -> Nothing
typecheck (EPair e1 e2) = do
  t1 <- typecheck e1
  t2 <- typecheck e2
  case (t1, t2) of
    (t1, t2) -> pure TPair
typecheck (EFst (EPair e1 _)) = do
  t1 <- typecheck e1
  case t1 of
     TInt -> pure TInt
     TBool -> pure TBool
     TPair -> pure TPair
typecheck (ESnd (EPair _ e2)) = do
  t2 <- typecheck e2
  case t2 of
     TInt -> pure TInt
     TBool -> pure TBool
     TPair -> pure TPair

-- Note how the form of the typechecking function closely resembles the
-- evaluation function. This is how we can think of typechecking as an *static
-- approximation* of the runtime behavior of a program.

t1 = typecheck e1   -- Just TInt


-- Finally, we can combine typechecking and interpretation into a single
-- function that first typechecks our program and only interprets it if
-- typechecking is successful:

safeEval :: Exp -> Maybe Val
safeEval e =
  case typecheck e of
    Just _ -> eval e
    _      -> Nothing

v1' = safeEval e1    -- Just (VInt 6)

v3' = safeEval e3
v4' = safeEval e4
v5' = safeEval e5

-- If our typechecker is correct, then we know that safeEval returns
-- Nothing` iff `typecheck e` returns `Nothing`.  That is, evaluation of our
-- program never "goes wrong" by performing an invalid operation!

--------------------------------------------------------------------------------
-- Conditionals
--------------------------------------------------------------------------------

-- Now that you've seen how type checking is implemented, let's cycle back
-- and develop a typing rule for conditionals and then implement it in the code
-- above.  Critically, note that a conditional expression in Haskell requires
-- the types of the branches to be equal.  For example:
--
--     if True then 0 else False
--
-- does not typecheck because the if-then and else-branch have different types
-- (int and bool, respectively). Write down typechecking rules for conditionals
-- in the space below that reflects this fact:
--
--     e1 : bool   e2 : t1   e3 : t1           
--     ------------------------------------- :: t-if
--     if e1 then e2 else e3 : t1
--
-- And then implement the rule in our type checker above.  Make sure that your
-- implementation works on this example and others of your own design.

t2 = typecheck e2   -- Just TInt
v2' = safeEval e2   -- Just (VInt 1)

--------------------------------------------------------------------------------
-- Extra Features: Pairs
--------------------------------------------------------------------------------

-- And now let's extend our language with a new feature, pairs, to demonstrate
-- the extensibility of type checking and this approach to compiler
-- implementation.
--
-- Pairs add three additional expression forms to the language:
--
-- e ::= ... | (e1, e2) | fst e | snd e
--
-- + (e1, e2) is a pair literal which constructs a pair from two
--   sub-expressions, e1 and e2.
-- + fst e is the left-projection function which evaluates e to a pair and then
--   returns the left-hand element of the pair ("projects" it out).
-- + snd e is the right-projection function which fetches the right-hand
--   component of the pair.
--
-- The pair (v1, v2) is a value whenever its sub-components are also values.
-- This implies that pairs add a new value form as well:
--
-- + v ::= ... | (v1, v2)
--
-- Pairs also add a new type to the language:
--
-- t ::= ... | t1 * t2
--
-- + t1 * t2 denotes the type of a pair whose left-hand components have type t1
--   and right-hand components have type t2.
--
-- For example:
--
--   fst (1 + 1, False) -->* 2
--   if (snd (0, 1) == 1) then False else (fst (True, False)) -->* False
--
-- 1. Add:
--
--    + Three new forms to the Exp datatype,
--    + A new form to the Val datatype, and
--    + A new form to the Typ datatype
--
--    to capture the new syntactic forms
--
-- 2. Implement new cases for the eval function for these new forms.
-- 3. Implement new cases for the typecheck function for these new forms.
--
-- Make sure to test your implementation by coming up with new test cases
-- that involve pairs and running them through eval and typecheck.

