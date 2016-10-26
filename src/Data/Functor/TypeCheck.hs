{-# language GADTs, TypeFamilies, GeneralizedNewtypeDeriving, RankNTypes, UndecidableInstances #-}
module Data.Functor.TypeCheck where

import Control.Monad.Free.Church

data TypeCheckF v t next where
  LookupCtx :: v -> (t -> next) -> TypeCheckF v t next
  ExtendCtx :: v -> t -> next -> TypeCheckF v t next

instance Functor (TypeCheckF v t) where
  fmap f (LookupCtx x k) = LookupCtx x (f . k)
  fmap f (ExtendCtx x ty k) = ExtendCtx x ty (f k)

lookupCtx :: MonadFree (TypeCheckF v t) m => v -> m t
lookupCtx v = liftF (LookupCtx v id)

extendCtx :: MonadFree (TypeCheckF v t) m => v -> t -> m a -> m a
extendCtx v t = wrap . ExtendCtx v t

data FFree g a where
       FPure   :: a -> FFree g a
       FImpure :: g x -> (x -> FFree g a) -> FFree g a

data FFC g a =
  FFC { runFFC :: forall r . (a -> r) -> (forall x . g x -> (x -> r) -> r) -> r }

instance Functor (FFree g) where
  fmap f (FPure a) = FPure (f a)
  fmap f (FImpure g k) = FImpure g (fmap f . k)

instance Functor (FFC g) where
  fmap f (FFC p) = FFC (\pur imp -> p (pur . f) imp)

eta :: g a -> FFC g a
eta eff = FFC (\pur imp -> imp eff pur)

-- fmap f (fmap g (FFC p))
-- = fmap f (FFC (\pur imp -> p (pur . g) imp))     by defn
-- = FFC (\pur' imp' -> (\pur imp -> p (pur . g) imp) (pur' . f) imp')  by defn
-- = FFC (\pur' imp' -> p ((pur' . f) . g) imp')  by beta
-- = FFC (\pur' imp' -> p (pur' . (f . g)) imp')  by assoc-compose
-- = fmap (f . g) (FFC p)                         by defn


instance Applicative (FFC g) where
  pure a = FFC (\pur _imp -> pur a)
  (FFC rf) <*> (FFC rx) = FFC (\pur imp -> rf (\f -> rx (pur . f) imp) imp)

-- pure id <*> v = v                            -- Identity
--
-- pure id <*> (FFC vp)
-- = (FFC (\pur _ -> pur id)) <*> (FFC vp)   by defn pure
-- = FFC (\pur' imp' -> (\pur _ -> pur id) (\f -> vp (pur' . f) imp') imp')   by defn (<*>)
-- = FFC (\pur' imp' -> (\f -> vp (pur' . f) imp') id)   by beta
-- = FFC (\pur' imp' -> vp (pur' . id) imp')             by beta
-- = FFC (\pur' imp' -> vp pur' imp')                    by compose-id
-- = FFC vp                                              by eta

-- pure f <*> pure x = pure (f x)               -- Homomorphism
--
-- pure f <*> pure x
-- FFC (\pur _ -> pur f) <*> FFC (\pur' _-> pur' x)    by defn
-- FFC (\pur'' imp'' -> (\pur _ -> pur f) (\h -> (\pur' _ -> pur' x) (pur'' . h) imp'') imp'')  by defn
-- FFC (\pur'' imp'' -> (\h -> (\pur' -> pur' x) (pur'' . h) imp'') f)     by beta
-- FFC (\pur'' imp'' -> (\pur' _ -> pur' x) (pur'' . f) imp'')             by beta
-- FFC (\pur'' imp'' -> (pur'' . f) x)                                     by beta
-- FFC (\pur'' _ -> pur'' (f x))                                           by defn-compose
-- pure (f x)                                                              by defn

-- u <*> pure y = pure (\k -> k y) <*> u              -- Interchange
--
-- FFC ru <*> FFC (\pur _ -> pur y)           -- by defn
-- FFC (\pur' imp' -> ru (\u -> (\pur _ -> pur y) (pur' . u) imp') imp')   -- by defn
-- FFC (\pur' imp' -> ru (\u -> (pur' . u) y) imp')     -- by beta
-- FFC (\pur' imp' -> ru (\u -> pur' (u y)) imp')       -- by beta
-- FFC (\pur' imp' -> ru (\u -> pur' ((\k -> k y) u)) imp')   -- by beta
-- FFC (\pur' imp' -> ru (\u -> (pur' . (\k -> k y)) u) imp') -- by defn-compose
-- FFC (\pur' imp' -> ru (pur' . (\k -> k y)) imp')             -- by eta
-- FFC (\pur' imp' -> (\f -> ru (pur' . f) imp') (\k -> k y))   -- by beta
-- FFC (\pur' imp' -> (\pur _ -> pur (\k -> k y)) (\f -> ru (pur' . f) imp') imp') -- by defn
-- FFC (\pur _ -> pur (\k -> k y)) <*> FFC ru

-- pure compose <*> u <*> v <*> w = u <*> (v <*> w) -- Composition
-- omg tedious

instance Monad (FFC g) where
  return = pure
  mx >>= f = FFC (\pur imp -> runFFC mx (\a -> runFFC (f a) pur imp) imp)

-- return a >>= f = f a
--
-- FFC (\pur' _ -> pur' a) >>= f
-- FFC (\pur imp -> (\pur' _ -> pur' a) (\x -> runFFC (f x) pur imp) imp)   by defn
-- FFC (\pur imp -> (\x -> runFFC (f x) pur imp) a)   by beta
-- FFC (\pur imp -> runFFC (f a) pur imp)    by beta
-- FFC (runFFC (f a))   by eta
-- f a  by eta


-- (FFC mp) >>= return = (FFC mp)
-- 
-- FFC mp >>= (\x -> FFC (\pur' _ -> pur' x))   by defn
-- FFC (\pur imp -> mp (\a -> runFFC ((\x -> FFC (\pur' _ -> pur' x)) a) pur imp) imp)  by defn
-- FFC (\pur imp -> mp (\a -> runFFC (FFC (\pur' _ -> pur' a)) pur imp) imp)  by beta
-- FFC (\pur imp -> mp (\a -> pur a) imp)    by beta
-- FFC (\pur imp -> mp pur imp)              by eta
-- FFC mp                                    by eta

-- (FFC mp >>= f) >>= g = (FFC mp) >>= (\x -> f x >>= g)
--
-- FFC (\pur imp -> runFFC (FFC mp >>= f) (\a -> runFFC (g a) pur imp) imp)  -- by defn (>>=) outer
-- FFC (\pur imp -> runFFC (FFC (\pur' imp' -> mp (\b -> runFFC (f b) pur' imp') imp')) (\a -> runFFC (g a) pur imp) imp)  -- by defn (>>= inner)
-- FFC (\pur imp -> mp (\b -> runFFC (f b) (\a -> runFFC (g a) pur imp)) imp)  -- by beta
-- FFC (\pur imp -> mp (\b -> runFFC (FFC (\pur' imp' -> runFFC (f b) (\a -> runFFC (g a) pur' imp') imp')) pur imp) imp)    by beta
-- FFC (\pur imp -> mp (\b -> runFFC (f b >>= g) pur imp) imp)               by defn
-- FFC (\pur imp -> mp (\b -> runFFC ((\z -> f z >>= g) b) pur imp) imp)      by beta
-- FFC mp >>= (\z -> f z >>= g)      by defn


data Empty a

vacuous :: Empty a -> b
vacuous _ = error "vacuous"

interpEmpty' :: FFree Empty a -> a
interpEmpty' (FPure a) = a
interpEmpty' (FImpure emp k) = interpEmpty' (k (vacuous emp))

interpEmpty :: FFC Empty a -> a
interpEmpty (FFC ra) = ra id (\emp kx -> kx (vacuous emp))

f :: Monad m => Int -> m Int
f 0 = return 1
f 1 = return 1
f n = do
  i <- f (n - 1)
  j <- f (n - 2)
  return (i + j)

data Const b a = Const b

instance Functor (Const b) where
  fmap _f (Const b) = Const b

interpUnit' :: FFree (Const b) a -> Either b a
interpUnit' (FPure a) = Right a
interpUnit' (FImpure (Const b) _k) = Left b

interpUnit :: FFC (Const b) a -> Either b a
interpUnit (FFC p) = p Right (\(Const b) _k -> Left b) 

data Teletype a where
  ReadTTY :: Teletype Char
  WriteTTY :: Char -> Teletype ()

data TeleF next where
  ReadF :: (Char -> next) -> TeleF next
  WriteF :: Char -> next -> TeleF next

instance Functor TeleF where
  fmap f (ReadF k) = ReadF (f . k)
  fmap f (WriteF c k) = WriteF c (f k)

teleTo :: FFC Teletype a -> F TeleF a
teleTo (FFC p) = F (\ar telek -> p ar (\tty k -> case tty of
                                                   ReadTTY -> telek (ReadF k)
                                                   WriteTTY c -> telek (WriteF c (k ()))))

teleFrom :: F TeleF a -> FFC Teletype a
teleFrom (F q) = FFC (\pur imp -> q pur (\telek -> case telek of
                                            ReadF k -> imp ReadTTY k
                                            WriteF c k -> imp (WriteTTY c) (\() -> k)))

ttyIO :: FFC Teletype a -> IO a
ttyIO (FFC p) = p return (\tty k -> case tty of
                                      ReadTTY -> do
                                        c <- getChar
                                        k c
                                      WriteTTY c -> do
                                        putChar c
                                        k ())
readTTY :: FFC Teletype Char
readTTY = eta ReadTTY

writeTTY :: Char -> FFC Teletype ()
writeTTY = eta . WriteTTY

echo :: Int -> FFC Teletype ()
echo 0 = return ()
echo n = do
  c <- readTTY
  writeTTY c
  echo (n - 1)
  
echo' :: Int -> FFC Teletype ()
echo' n = teleFrom (teleTo (echo n))
-- f' :: Int -> FFree Unit a
-- f' = 
