module Test.DSL where

import Prelude
import Control.Monad.Free (Free, foldFree, liftF)
import Control.Comonad.Cofree (Cofree, buildCofree)
import Control.Comonad (class Comonad)
import Data.Functor.Day (type (⊗), runDay)
import Data.Functor.Day.Hom (type (⊸), runHom, hom, introHom)
import Data.Functor.Pairing (type (⋈), freeCofree, productCoproduct, sym)
import Data.Functor.Pairing.Co (Co, co, runCo)
import Data.Identity (Identity)
import Data.Newtype (unwrap, wrap)
import Unsafe.Coerce (unsafeCoerce)
import Data.Functor.Coproduct (Coproduct, left, right)
import Data.Functor.Product (Product, product)
import Data.Tuple (Tuple(..))
import React.DOM as D
import React.DOM.Props as P
import React.Explore (Component, UI)


{-

Let 'C' be the functor category. For a given functor 'g', define the functor 'F: C^op -> Set' by

    f |--> f ⊗ g ~> Identity
    α :: f ~> f' |--> . hoistDay1 α :: (f' ⊗ g ~> Identity) ~> (f ⊗ g ~> Identity).

Because ⊗ has a right adjoint, denoted by ⊸ , it follows that F is representable, namely

    F f ~ Hom (f, g ⊸ Identity).

We have another name for 'g ⊸ Identity', namely 'Co g', so it follows that F is representable by 'Co g'.

In order to realize the adjunction as an isomorphism of Hom sets, we can use the following functions from
Data.Functor.Day.Hom:

introHom :: forall f g h. (f ⊗ g ~> h) -> f ~> g ⊸ h

elimHom :: forall f g h. Functor g => (f ~> g ⊸ h) -> f ⊗ g ~> h

-}



-- co :: forall w a. (forall r. w (a -> r) -> r) -> Co w a
-- runHom :: forall f g a r. Hom f g a -> f (a -> r) -> g r

makeCoRep :: forall g . (g ⊸ Identity) ~> Co g
makeCoRep hom = unsafeCoerce co $ unwrap <<< runHom hom

makeHomRep :: forall g . Co g ~> g ⊸ Identity
makeHomRep c = unsafeCoerce hom $ (wrap :: forall a . a -> Identity a) <<< runCo c

embedEffects :: forall f g .
                Functor f
             => Comonad g
             => (f ⊗ g ~> Identity)
             -> (Free f ~> Co g)
embedEffects phi = foldFree (makeCoRep <<< introHom phi)

embedEffects' :: forall f g .
                 Functor f
              => Functor g
              => f ⋈ g
              -> (Free f ~> Co (Cofree g))
embedEffects' p = embedEffects annhilateDual <<< liftF
  where
    annhilateDual :: Free f ⊗ Cofree g ~> Identity
    annhilateDual = wrap <<< runDay (freeCofree p)


-- | Free Monad Commands and Definition
data AddF a = AddF Int a

derive instance functorAddF :: Functor AddF

data TotalF a = TotalF (Int -> a)

derive instance functorTotalF :: Functor TotalF

type CalcF = Coproduct AddF TotalF

type Calc = Free CalcF

add :: Int -> Calc Unit
add n = liftF <<< left $ AddF n unit

total :: Calc Int
total = liftF <<< right $ TotalF id

-- | Cofree Comonad Interpreter Definitions
data CoAddF a = CoAddF (Int -> a)

derive instance functorCoAddF :: Functor CoAddF

data CoTotalF a = CoTotalF (Tuple Int a)

derive instance functorCoTotalF :: Functor CoTotalF

type CoCalcF = Product CoAddF CoTotalF

type CoCalc = Cofree CoCalcF

coAdd :: Int -> CoAddF Int
coAdd currentCount = CoAddF $ \n -> n + currentCount

coTotal :: Int -> CoTotalF Int
coTotal currentCount = CoTotalF (Tuple currentCount currentCount)

-- pairings

addP :: CoAddF ⋈ AddF
addP f (CoAddF g) (AddF n b) = f (g n) b

totalP :: CoTotalF ⋈ TotalF
totalP f (CoTotalF (Tuple n a)) (TotalF g) = f a (g n)

calcP :: CalcF ⋈ CoCalcF
calcP = sym calcP'
  where
    calcP' :: CoCalcF ⋈ CalcF
    calcP' = productCoproduct addP totalP

--------------------------------------------------------------------------------

calcInterpreter :: CoCalc Unit
calcInterpreter =
  let start = 0
      next wa = Tuple unit (coAdd wa `product` coTotal wa)
  in buildCofree next start

calcExample :: Component CoCalc
calcExample = buildCofree (\count -> Tuple (render count) (coAdd count `product` coTotal count)) 0 where
  embed :: Calc ~> Co CoCalc
  embed = embedEffects' calcP
  render :: Int -> UI (Co (CoCalc) Unit)
  render count send =
    D.div' [ D.p' [ D.text ("State: " <> show count) ]
           , D.button [ P.onClick \_ ->
                         send (embed $ add 1)
                      ]
                      [ D.text "Increment"
                      ]
           ]
