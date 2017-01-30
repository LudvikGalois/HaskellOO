{-# Language DataKinds, KindSignatures, TypeOperators, GADTs, MultiParamTypeClasses
  , FlexibleInstances, UndecidableInstances, FlexibleContexts
  , TypeInType, ScopedTypeVariables, ExplicitNamespaces, TypeFamilies, NoMonomorphismRestriction
  , RankNTypes #-}
-- This kind of just naturally evolved from a sleep deprived state.
-- I'm not sure how much faster I can make it - Haskell just wasn't designed
-- with type level programming in mind. I'm about 95% sure that all the uses
-- of unsafeCoerce are safe, but I was super tired when I wrote this...
module HaskellOO (build, newMethod, (.=.), (.*.), (.>.), (#), (<:)
                 , module Data.Proxy, module Data.IORef, new, returnIO, object)   where

import Data.Kind 
import Data.Proxy
import GHC.TypeLits hiding (type (*))
import Data.Type.Equality
import Data.IORef
import Control.Monad.Fix
import Unsafe.Coerce
import Language.Haskell.TH

data BTree a = Null | Node a (BTree a) (BTree a)

-- GADTs <3
data PTree (l :: BTree *) where
  PNull :: PTree 'Null
  PNode :: (KnownSymbol s) => Tagged s e -> PTree l -> PTree r
    -> PTree ('Node (Tagged s e) l r)

data N = Z | S N

type family Length a where
  Length '[] = 'Z
  Length (x ': xs) = 'S (Length xs)

type family Halve a where
  Halve 'Z = 'Z
  Halve ('S 'Z) = 'Z
  Halve ('S ('S n)) = 'S (Halve n)

type family Take n a where
  Take 'Z _ = '[]
  Take ('S m) '[] = '[]
  Take ('S m) (x ': xs) = x ': (Take m xs)

type family Drop n a where
  Drop 'Z x = x
  Drop ('S m) '[] = '[]
  Drop ('S m) (x ': xs) = Drop m xs

type family MidSplit a  where
  MidSplit xs = '(Take (Halve (Length xs)) xs, Drop (Halve (Length xs))  xs)

type family Fst a where
  Fst '(x,y) = x

type family Snd a where
  Snd '(x,y) = y

type family Head a where
  Head (x ': xs) = x

type family Tail a where
  Tail (x ': xs) = xs

type family ToTree a where
  ToTree '[] = 'Null
  ToTree '[x] = 'Node x 'Null 'Null
  ToTree (x ': y ': zs) = 'Node (Head (Snd (MidSplit (x ': y ': zs))))
                                (ToTree (Fst (MidSplit (x ': y ': zs))))
                                (ToTree (Tail (Snd (MidSplit (x ': y ': zs)))))

plength :: PList a -> Int
plength PNil = 0
plength (PCons x xs) = 1 + plength xs

-- The following two functions aren't safe - don't call them by themselves!
ptake :: Int -> PList a -> PList b
ptake 0 x = unsafeCoerce PNil
ptake n PNil = unsafeCoerce PNil
ptake n (PCons x xs) = unsafeCoerce $ PCons x (ptake (n-1) xs)

pdrop :: Int -> PList a -> PList b
pdrop 0 x = unsafeCoerce x
pdrop _ PNil = unsafeCoerce PNil
pdrop n (PCons x xs) = unsafeCoerce (pdrop (n-1) xs)

split' :: ('(b,c) ~ MidSplit a) => PList a -> (PList b, PList c)
split' xs = (ptake halfLength xs, pdrop halfLength xs)
  where halfLength = plength xs `div` 2

toTree :: (PList a) -> PTree (ToTree a)
toTree PNil = PNull
toTree (PCons x PNil) = PNode x PNull PNull
toTree a@(PCons x (PCons y zs)) = case split' a of
  (l, (PCons x r)) -> unsafeCoerce $ PNode x (toTree l) (toTree r)

newtype Tagged (a :: Symbol) (b :: *) = Tagged b

type family Choose (a :: Ordering) b c d where
  Choose 'LT b _ _ = b
  Choose 'EQ _ c _ = c
  Choose 'GT _ _ d = d

data PList (l :: [*]) where 
  PNil :: PList '[]
  PCons :: (KnownSymbol s) => Tagged s b -> PList a -> PList (Tagged s b ': a)

type family Merge a b where
  Merge ('[]) ('[]) = ('[])
  Merge x ('[]) = x
  Merge ('[]) x = x
  Merge (Tagged xsym xval ': xs) (Tagged ysym yval ': ys) =
    Choose (CmpSymbol xsym ysym)
      (Tagged xsym xval ': (Merge xs (Tagged ysym yval ': ys)))
      (Tagged xsym xval ': (Merge xs (Tagged ysym yval ': ys)))
      (Tagged ysym yval ': (Merge (Tagged xsym xval ': xs) ys))

merge :: (PList a) -> (PList b) -> (PList (Merge a b))
merge PNil PNil = PNil
merge PNil x = x
merge x PNil = x
merge a@(PCons x xs) b@(PCons y ys) = merge' a b 

merge' :: PList (Tagged xsym xval ': xs) -> PList (Tagged ysym yval ': ys) ->
  PList (Merge (Tagged xsym xval ': xs) (Tagged ysym yval ': ys))
merge' a@(PCons (x :: Tagged xsym' xval') xs) b@(PCons (y :: Tagged ysym' yval') ys) = case compare (symbolVal (Proxy :: Proxy xsym')) (symbolVal (Proxy :: Proxy ysym')) of
  LT -> unsafeCoerce $ PCons x (merge xs b)
  EQ -> unsafeCoerce $ PCons x (merge xs b)
  GT -> unsafeCoerce $ PCons y (merge a ys)

type family Mergesort a where
  Mergesort '[] = '[]
  Mergesort '[x] = '[x]
  Mergesort (x ': y ': zs) = Merge (Mergesort (Fst (MidSplit (x ': y ': zs)))) (Mergesort (Snd (MidSplit (x ': y ': zs))))

mergesort :: PList a -> PList (Mergesort a)
mergesort PNil = PNil
mergesort (PCons x PNil) = PCons x PNil
mergesort (PCons x (PCons y zs)) = merge (mergesort l) (mergesort r)
  where (l,r) = split' (PCons x (PCons y zs))

type family MethodLookup (s :: Symbol) t where
  MethodLookup s 'Null = TypeError (Text "Method not found: \"" :<>: Text s :<>: Text "\"")
  MethodLookup s ('Node (Tagged xsym xval) l r) =
    Choose (CmpSymbol s xsym) (MethodLookup s l) xval (MethodLookup s r)

methodLookup :: (KnownSymbol s) => (Proxy s) -> PTree a -> MethodLookup s a
methodLookup p (PNode ((Tagged x) :: Tagged xsym xval) l r) = case compare (symbolVal p) (symbolVal (Proxy :: Proxy xsym)) of
  LT -> unsafeCoerce $ methodLookup p l
  EQ -> unsafeCoerce $ x
  GT -> unsafeCoerce $ methodLookup p r

infixr 9 # 
infixr 2 .*.
infixr 2 .>.
infixr 4 .=.

-- | Call a method on an object
(#) :: (KnownSymbol s) => (PTree t) -> Proxy s -> MethodLookup s t
(#) = flip methodLookup

type family Insert a b where
  Insert (Tagged xsym xval) '[] = '[Tagged xsym xval]
  Insert (Tagged xsym xval) (Tagged xsym xval ': xs) = (Tagged xsym xval ': xs)
  Insert (Tagged xsym xval) (Tagged xsym yval ': xs) = TypeError (Text "couldn't insert")
  Insert (Tagged xsym xval) (Tagged ysym yval ': xs) =
    Choose (CmpSymbol xsym ysym)
      (Tagged xsym xval ': Tagged ysym yval ': xs)
      (Tagged xsym xval ': xs)
      (Tagged ysym yval ': (Insert (Tagged xsym xval) xs))

insert :: (KnownSymbol s) => (Tagged s a) -> (PList b) -> PList (Insert (Tagged s a) b)
insert x PNil = PCons x PNil
insert (x :: Tagged xsym xval) (PCons (y :: Tagged ysym yval) ys) = case compare (symbolVal (Proxy :: Proxy xsym)) (symbolVal (Proxy :: Proxy ysym)) of
  LT -> unsafeCoerce $ PCons x (PCons y ys)
  EQ -> unsafeCoerce $ PCons x ys
  GT -> unsafeCoerce $ PCons y (insert x ys)

type family Concat a b where
  Concat '[] b = b
  Concat (x ': xs) b = x ': (Concat xs b)

pConcat :: PList a -> PList b -> PList (Concat a b)
pConcat PNil xs = xs
pConcat (PCons x xs) ys = PCons x (pConcat xs ys)

type family Flatten a where
  Flatten 'Null = '[]
  Flatten ('Node x l r) = Concat (Flatten l) (x ': Flatten r)

flatten :: PTree a -> PList (Flatten a)
flatten PNull = PNil 
flatten (PNode x l r) = pConcat (flatten l) (PCons x (flatten r))

toString :: Proxy "toString"
toString = Proxy

printSelf :: Proxy "printSelf"
printSelf = Proxy

-- | Define a method
(.=.) :: Proxy s -> a -> Tagged s a
_ .=. s = Tagged s
  
-- | Add a method to an object description
(.*.) :: (KnownSymbol xsym) => (Tagged xsym xval) -> (PList xs) -> PList (Insert (Tagged xsym xval) xs)
(.*.) = insert 

-- | Inherit from
(.>.) :: (KnownSymbol xsym) => (Tagged xsym xval) -> (PTree tree) -> PList (Insert (Tagged xsym xval) (Flatten tree))
x .>. t = x .*. flatten t

-- | Return, monomorphised for IO
returnIO :: a -> IO a
returnIO = return

-- | Take an object description and turn it into
-- an object
build = returnIO . toTree . mergesort

type Object = PTree
type Constructor a = (Object a -> IO (Object a))

-- | Given a constructor, create an object
new :: Constructor a -> IO (Object a)
new = mfix

object self = do
  build $  toString .=. (returnIO "An Object")
       .*. printSelf .=. (self # toString >>= putStrLn)
       .*. PNil

downcast :: PTree a -> PTree b -> PTree (ToTree (Downcast' (Flatten a) (Flatten b)))
downcast a b = toTree $ downcast' (flatten a) (flatten b)

toProxy :: a -> Proxy a
toProxy _ = Proxy

type family Downcast' a b where
  Downcast' '[] '[] = '[]
  Downcast' (x ': xs) '[] = '[]
  Downcast' '[] (x ': xs) = '[]
  Downcast' (Tagged xsym val ': xs) (Tagged ysym val ': ys) = 
   Choose (CmpSymbol xsym ysym)
      (Downcast' xs (Tagged ysym val ': ys))
      (Tagged xsym val ': (Downcast' xs (Tagged ysym val ': ys)))
      (Downcast' (Tagged xsym val ': xs) ys)
  Downcast' (Tagged xsym xval ': xs) (Tagged ysym yval ': ys) = 
   Choose (CmpSymbol xsym ysym)
      (Downcast' xs (Tagged ysym yval ': ys))
      (TypeError (Text "Method types of <" :<>: Text xsym :<>: Text "> don't match" :$$:
                 Text "(" :<>: ShowType xval :<>: Text " /= " :<>: ShowType yval :<>: Text ")"))
      (Downcast' (Tagged xsym xval ': xs) ys)

downcast' :: PList a -> PList b -> PList (Downcast' a b)
downcast' PNil PNil = PNil
downcast' (PCons x xs) PNil = PNil
downcast' PNil (PCons y ys) = PNil
downcast' (PCons (x :: Tagged xsym xval) xs) (PCons (y :: Tagged ysym yval) ys)
  = case compare (symbolVal (Proxy :: Proxy xsym)) (symbolVal (Proxy :: (Proxy ysym))) of
  LT -> unsafeCoerce $ downcast' xs (PCons y ys)
  EQ -> unsafeCoerce $ PCons y (downcast' xs ys)
  GT -> unsafeCoerce $ downcast' (PCons x xs) ys

-- Least upper bound cons
lubcons :: (c ~ (Downcast' (Flatten a) (Flatten b)), c ~ (Downcast' (Flatten b) (Flatten a))) => (PTree a) -> [(PTree b)] -> [(PTree (ToTree c))]
lubcons x xs = unsafeCoerce (x' : xs')
  where x' = downcast (head xs) x
        xs' = map (downcast x) xs

infixr 5 <:
(<:) = lubcons

newMethod :: String -> Q [Dec]
newMethod s = do
  n <- lookupValueName s -- Do nothing if defined
  case n of
    Nothing -> do
      name <- newName s
      (Just proxy) <- lookupTypeName "Proxy"
      (Just proxyv) <- lookupValueName "Proxy"
      let sig = SigD name (AppT (ConT proxy) (LitT (StrTyLit s)))
      let def = (FunD name [Clause [] (NormalB (ConE proxyv)) []])
      return [sig, def]
    _ -> return []
