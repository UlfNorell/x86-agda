
module Container.Path where

open import Prelude

data Path {a b} {I : Set a} (R : I → I → Set b) (i : I) : I → Set (a ⊔ b) where
  []  : Path R i i
  _∷_ : ∀ {j k} → R i j → Path R j k → Path R i k

_==>_ : ∀ {a b c} {I : Set a} → (I → I → Set b) → (I → I → Set c) → Set (a ⊔ b ⊔ c)
R ==> S = ∀ {i j} → R i j → S i j

module _ {a b} {I : Set a} {R : I → I → Set b} where

  infixr 5 _<+>_
  _<+>_ : ∀ {i j k} → Path R i j → Path R j k → Path R i k
  []       <+> ys = ys
  (x ∷ xs) <+> ys = x ∷ xs <+> ys

  module _ {c} {S : I → I → Set c} where

    foldPath : (∀ {i j k} → R i j → S j k → S i k) → (∀ {i} → S i i) → Path R ==> S
    foldPath f z []       = z
    foldPath f z (x ∷ xs) = f x (foldPath f z xs)

    mapPath : (R ==> S) → Path R ==> Path S
    mapPath f []       = []
    mapPath f (x ∷ xs) = f x ∷ mapPath f xs
