module Test.DSL where

import Prelude
import Control.Monad.Free (Free, foldFree, liftF)
import Control.Comonad.Cofree (Cofree)
import Control.Comonad (class Comonad)
import Data.Functor.Day (type (⊗), day, runDay)
import Data.Functor.Day.Hom (type (⊸), runHom, hom, introHom)
import Data.Functor.Pairing (type (⋈), freeCofree)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Functor.Pairing.Co (Co, co, runCo)
import Data.Identity (Identity)
import Data.Newtype (unwrap, wrap)
import Unsafe.Coerce (unsafeCoerce)
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
             => MonadRec (Co g)
             => (f ⊗ g ~> Identity)
             -> (Free f ~> Co g)
embedEffects phi = foldFree (makeCoRep <<< introHom phi)

embedEffects' :: forall f g .
                 Functor f
              => Comonad g
              => MonadRec (Co (Cofree g))
              => f ⋈ g
              -> (Free f ~> Co (Cofree g))
embedEffects' p = embedEffects annhilateDual <<< doubleFree
  where
    doubleFree :: Free f ~> Free (Free f)
    doubleFree = liftF
    annhilateDual :: Free f ⊗ Cofree g ~> Identity
    annhilateDual = wrap <<< runDay (freeCofree p)
