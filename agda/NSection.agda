module NSection where

open import Data.Empty
open import Data.Unit
open import Data.Sum     hiding (map)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Fin
open import Data.Vec     renaming (map to vecMap ; foldr to vecFoldr)

open import Function

open import Relation.Binary.PropositionalEquality hiding ( [_] )

open import Level using (Level)

-- Universe/algebra of n-ary functors.
data F : ℕ → Set₁ where
  Zero : {n : ℕ} → F n                -- void
  K    : {n : ℕ} → Set → F n          -- const
  X    : {n : ℕ} → Fin n → F n        -- projection, i.e. Id
  _⊕_  : {n : ℕ} → F n → F n → F n    -- sum
  _⊗_  : {n : ℕ} → F n → F n → F n    -- product

  -- Can't do least fixed point because it makes Agda unhappy, and I don't
  -- want to move to full-fledged containers right now
  -- μ    : {n : ℕ} → Fin (suc n) → F n

infixl 6 _⊕_
infixl 7 _⊗_

-- One is a synonym for the constantly ⊤ functor
pattern One = K ⊤

pattern X₀ = X zero
pattern X₁ = X (suc zero)
pattern X₂ = X (suc (suc zero))

sucX : {n : ℕ} → F n → F (suc n)
sucX Zero = Zero
sucX (K A) = K A
sucX (X i) = X (suc i)
sucX (f ⊕ g) = sucX f ⊕ sucX g
sucX (f ⊗ g) = sucX f ⊗ sucX g

-- Sets n = Set → Set → ... → Set  with n arrows
Sets : ℕ → Set₁
Sets zero = Set
Sets (suc n) = Set → Sets n

-- Generalized currying: (Set × Set × ... × Set) → Set ≅ Set → Set → ... → Set
Curry : {n : ℕ} → (Vec Set n → Set) → Sets n
Curry {zero} f = f []
Curry {suc n} f A = Curry (f ∘ _∷_ A)

-- Interpretation function for elements of the universe F.  A code of
-- type F n represents an n-ary functor, here represented as Set^n → Set.
⟦_⟧ : {n : ℕ} → F n → Vec Set n → Set
⟦_⟧ Zero _ = ⊥
⟦_⟧ (K A) _ = A
⟦_⟧ (X zero) As = head As
⟦_⟧ (X (suc i)) As = ⟦ X i ⟧ (tail As)
⟦_⟧ (f ⊕ g) As = ⟦ f ⟧ As ⊎ ⟦ g ⟧ As
⟦_⟧ (f ⊗ g) As = ⟦ f ⟧ As × ⟦ g ⟧ As

-- Interpretation as Set → ... → Set
⟦_⟧′ : {n : ℕ} → F n → Sets n
⟦ f ⟧′ = Curry ⟦ f ⟧

open import Function.Inverse as Inv using (_↔_; module Inverse)

_≅_ : {n : ℕ} → F n → F n → Set₁
_≅_ {n} f g = ∀ (As : Vec Set n) → ⟦ f ⟧ As ↔ ⟦ g ⟧ As

-- n-ary maps between Set^n
Map : {n : ℕ} → Vec Set n → Vec Set n → Set
Map [] [] = ⊤
Map (A ∷ As) (B ∷ Bs) = (A → B) × Map As Bs

-- The identity n-ary map
Id : {n : ℕ} → (As : Vec Set n) → Map As As
Id [] = tt
Id (A ∷ As) = id , Id As

-- composition of n-ary maps
Comp : {n : ℕ} {As Bs Cs : Vec Set n} → Map Bs Cs → Map As Bs → Map As Cs
Comp {zero} {[]} {[]} {[]} _ _ = tt
Comp {suc n} {A ∷ As} {B ∷ Bs} {C ∷ Cs} (B→C , Bs→Cs) (A→B , As→Bs)
  = B→C ∘ A→B , Comp Bs→Cs As→Bs

-- interpretation of F is functorial
map : ∀ {n : ℕ} {As Bs : Vec Set n} → (f : F n) → Map As Bs → ⟦ f ⟧ As → ⟦ f ⟧ Bs
map Zero _ ()
map (K A) _ fAs = fAs
map {As = _ ∷ _} {_ ∷ _} (X zero) (A→B , _) fAs = A→B fAs
map {As = _ ∷ _} {_ ∷ _} (X (suc i)) (_ , m) fAs = map (X i) m fAs
map (f ⊕ g) m fAs = Data.Sum.map (map f m) (map g m) fAs
map (f ⊗ g) m fAs = Data.Product.map (map f m) (map g m) fAs

-- Functor law: preservation of identity
pres-id : ∀ {n : ℕ} {As : Vec Set n} → (f : F n) → {fAs : ⟦ f ⟧ As}
        → (map f (Id As) fAs ≡ fAs)
pres-id Zero {()}
pres-id (K A) = refl
pres-id {As = _ ∷ _} (X zero) = refl
pres-id {As = _ ∷ _} (X (suc i)) = pres-id (X i)
pres-id (f ⊕ g) {inj₁ fAs} = cong inj₁ (pres-id f)
pres-id (f ⊕ g) {inj₂ gAs} = cong inj₂ (pres-id g)
pres-id (f ⊗ g) {fAs , gAs} = cong₂ _,_ (pres-id f) (pres-id g)

postulate ext : ∀ {A B : Set} {f g : A → B} → ({x : A} → f x ≡ g x) → f ≡ g

pres-id-ext : ∀ {n : ℕ} {As : Vec Set n} → (f : F n) → map f (Id As) ≡ id
pres-id-ext f = ext (pres-id f)

-- Functor law: preservation of composition
pres-∘ : ∀ {n : ℕ} {As Bs Cs : Vec Set n} → (f : F n)
       → {g : Map As Bs} → {h : Map Bs Cs} → {fAs : ⟦ f ⟧ As}
       → (map f h (map f g fAs) ≡ map f (Comp h g) fAs)
pres-∘ Zero {fAs = ()}
pres-∘ (K A) = refl
pres-∘ {As = _ ∷ _} {Bs = _ ∷ _} {Cs = _ ∷ _} (X zero) = refl
pres-∘ {As = _ ∷ _} {Bs = _ ∷ _} {Cs = _ ∷ _} (X (suc i)) = pres-∘ (X i)
pres-∘ (f ⊕ g) {fAs = inj₁ fAs} = cong inj₁ (pres-∘ f)
pres-∘ (f ⊕ g) {fAs = inj₂ gAs} = cong inj₂ (pres-∘ g)
pres-∘ (f ⊗ g) {fAs = fAs , gAs} = cong₂ _,_ (pres-∘ f) (pres-∘ g)

pres-∘-ext : ∀ {n : ℕ} {As Bs Cs : Vec Set n} → (f : F n)
       → {g : Map As Bs} → {h : Map Bs Cs} → {fAs : ⟦ f ⟧ As}
       → map f h ∘ map f g ≡ map f (Comp h g)
pres-∘-ext f = ext (pres-∘ f)

------------------------------------------------------------
-- Dissection
------------------------------------------------------------

-- Start with basic 2-dissection, as in Jokers & Clowns paper

-- D₂ : F 1 → F 2
-- D₂ Zero = Zero
-- D₂ (K _) = Zero
-- D₂ (X _) = One
-- D₂ (f ⊕ g) = D₂ f ⊕ D₂ g
-- D₂ (f ⊗ g) = (D₂ f ⊗ R g) ⊕ (L f ⊗ D₂ g)
-- D₂ (L f) = D₂ f
-- D₂ (R f) = D₂ f

-- Should try redoing this with pointed things.  Also, seems like this is doing a lot of repeated work.

-- right : (f : F 1) → {j c : Set} → (⟦ f ⟧′ j ⊎ (⟦ D₂ f ⟧′ c j × c)) → ((j × ⟦ D₂ f ⟧′ c j) ⊎ ⟦ f ⟧′ c)
-- right Zero (inj₁ ())
-- right Zero (inj₂ (() , _))
-- right (K A) (inj₁ a) = inj₂ a
-- right (K A) (inj₂ (() , _))
-- right (X zero) (inj₁ j) = inj₁ (j , tt)
-- right (X (suc ()))
-- right (X zero) (inj₂ (tt , c)) = inj₂ c
-- right (f ⊕ g) (inj₁ (inj₁ fj))       with right f (inj₁ fj)
-- ...                                  | inj₁ (j , f'cj)  = inj₁ (j , inj₁ f'cj)
-- ...                                  | inj₂ fc          = inj₂ (inj₁ fc)
-- right (f ⊕ g) (inj₁ (inj₂ gj))       with right g (inj₁ gj)
-- ...                                  | inj₁ (j , g'cj)  = inj₁ (j , inj₂ g'cj)
-- ...                                  | inj₂ gc          = inj₂ (inj₂ gc)
-- right (f ⊕ g) (inj₂ (inj₁ f'cj , c)) with right f (inj₂ (f'cj , c))
-- ...                                  | inj₁ (j , f'cj₂) = inj₁ (j , inj₁ f'cj₂)
-- ...                                  | inj₂ fc          = inj₂ (inj₁ fc)
-- right (f ⊕ g) (inj₂ (inj₂ g'cj , c)) with right g (inj₂ (g'cj , c))
-- ...                                  | inj₁ (j , g'cj₂) = inj₁ (j , inj₂ g'cj₂)
-- ...                                  | inj₂ gc          = inj₂ (inj₂ gc)
-- right (f ⊗ g) (inj₁ (fj , gj))       with right f (inj₁ fj)
-- ...                                  | inj₁ (j , f'cj)  = inj₁ (j , (inj₁ (f'cj , gj)))
-- ...                                  | inj₂ fc
--                                        with right g (inj₁ gj)
-- ...                                    | inj₁ (j , g'cj) = inj₁ (j , (inj₂ (fc , g'cj)))
-- ...                                    | inj₂ gc         = inj₂ (fc , gc)
-- right (f ⊗ g) (inj₂ (inj₁ (f'cj , gj) , c)) with right f (inj₂ (f'cj , c))
-- ...                                         | inj₁ (j , f'cj₂)  = inj₁ (j , (inj₁ (f'cj₂ , gj)))
-- ...                                         | inj₂ fc
--                                               with right g (inj₁ gj)
-- ...                                           | inj₁ (j , g'cj) = inj₁ (j , (inj₂ (fc , g'cj)))
-- ...                                           | inj₂ gc         = inj₂ (fc , gc)
-- right (f ⊗ g) (inj₂ (inj₂ (fc , g'cj) , c)) with right g (inj₂ (g'cj , c))
-- ...                                         | inj₁ (j , g'cj₂) = inj₁ (j , (inj₂ (fc , g'cj₂)))
-- ...                                         | inj₂ gc = inj₂ (fc , gc)
-- right (L f) l = right f l
-- right (R f) l = right f l


-- The below implementation more closely matches Conor's from "Jokers & Clowns"

-- ⊕f : (f g : F 1) {j c : Set} → (j × ⟦ D₂ f ⟧′ c j) ⊎ ⟦ f ⟧′ c → (j × ⟦ D₂ (f ⊕ g) ⟧′ c j) ⊎ ⟦ f ⊕ g ⟧′ c
-- ⊕f _ _ (inj₁ (j , f'cj)) = inj₁ (j , inj₁ f'cj)
-- ⊕f _ _ (inj₂ fc) = inj₂ (inj₁ fc)

-- ⊕g : (f g : F 1) {j c : Set} → (j × ⟦ D₂ g ⟧′ c j) ⊎ ⟦ g ⟧′ c → (j × ⟦ D₂ (f ⊕ g) ⟧′ c j) ⊎ ⟦ f ⊕ g ⟧′ c
-- ⊕g _ _ (inj₁ (j , g'cj)) = inj₁ (j , inj₂ g'cj)
-- ⊕g _ _ (inj₂ gc) = inj₂ (inj₂ gc)

-- mutual
--   ⊗f : (f g : F 1) {j c : Set} → (j × ⟦ D₂ f ⟧′ c j) ⊎ ⟦ f ⟧′ c → ⟦ g ⟧′ j → (j × ⟦ D₂ (f ⊗ g) ⟧′ c j) ⊎ ⟦ f ⊗ g ⟧′ c
--   ⊗f f g (inj₁ (j , f'cj)) gj = inj₁ (j , (inj₁ (f'cj , gj)))
--   ⊗f f g (inj₂ fc) gj = ⊗g f g fc (right g (inj₁ gj))

--   ⊗g : (f g : F 1) {j c : Set} → ⟦ f ⟧′ c → (j × ⟦ D₂ g ⟧′ c j) ⊎ ⟦ g ⟧′ c → (j × ⟦ D₂ (f ⊗ g) ⟧′ c j) ⊎ ⟦ f ⊗ g ⟧′ c
--   ⊗g f g fc (inj₁ (j , g'cj)) = inj₁ (j , (inj₂ (fc , g'cj)))
--   ⊗g f g fc (inj₂ gc) = inj₂ (fc , gc)

--   right : (f : F 1) → {j c : Set} → (⟦ f ⟧′ j ⊎ (⟦ D₂ f ⟧′ c j × c)) → ((j × ⟦ D₂ f ⟧′ c j) ⊎ ⟦ f ⟧′ c)
--   right Zero (inj₁ ())
--   right Zero (inj₂ (() , _))
--   right (K A) (inj₁ a) = inj₂ a
--   right (K A) (inj₂ (() , _))
--   right (X zero) (inj₁ j) = inj₁ (j , tt)
--   right (X (suc ()))
--   right (X zero) (inj₂ (tt , c)) = inj₂ c
--   right (f ⊕ g) (inj₁ (inj₁ fj)) = ⊕f f g (right f (inj₁ fj))
--   right (f ⊕ g) (inj₁ (inj₂ gj)) = ⊕g f g (right g (inj₁ gj))
--   right (f ⊕ g) (inj₂ (inj₁ f'cj , c)) = ⊕f f g (right f (inj₂ (f'cj , c)))
--   right (f ⊕ g) (inj₂ (inj₂ g'cj , c)) = ⊕g f g (right g (inj₂ (g'cj , c)))
--   right (f ⊗ g) (inj₁ (fj , gj)) = ⊗f f g (right f (inj₁ fj)) gj
--   right (f ⊗ g) (inj₂ (inj₁ (f'cj , gj) , c)) = ⊗f f g (right f (inj₂ (f'cj , c))) gj
--   right (f ⊗ g) (inj₂ (inj₂ (fc , g'cj) , c)) = ⊗g f g fc (right g (inj₂ (g'cj , c)))
--   right (L f) x = right f x
--   right (R f) x = right f x

-- Next: try making types for pointed dissections?  Or go ahead and try generalizing to n-section?


------------------------------------------------------------
-- Generalized n-dissection
------------------------------------------------------------

Mat : {ℓ : Level} → ℕ → ℕ → Set ℓ → Set ℓ
Mat m n A = Fin m → Fin n → A

mkMat : {ℓ : Level} {A : Set ℓ} {m n : ℕ} → Vec (Vec A n) m → Mat m n A
mkMat v i j = lookup j (lookup i v)

mapMat : {ℓ : Level} {m n : ℕ} {A B : Set ℓ} → (A → B) → Mat m n A → Mat m n B
mapMat f m = λ i j → f (m i j)

matSum : {ℓ : Level} {m n : ℕ} {A : Set ℓ} → (A → A → A) → Mat m n A → Mat m n A → Mat m n A
matSum _⊞_ m₁ m₂ = λ i j → m₁ i j ⊞ m₂ i j

matProd : {ℓ : Level} {m n p : ℕ} {A : Set ℓ} → (A → A → A) → A → (A → A → A)
        → Mat m n A → Mat n p A → Mat m p A
matProd {n = n} {A = A} _⊞_ z _⊡_ m₁ m₂ = λ i j → vecFoldr (λ _ → A) _⊞_ z
                                                    (vecMap (λ k → m₁ i k ⊡ m₂ k j) (allFin n))

ifeq : {ℓ : Level} {n : ℕ} {A : Set ℓ} → Fin n → Fin n → A → A → A
ifeq zero zero x _ = x
ifeq zero (suc j) _ y = y
ifeq (suc i) zero _ y = y
ifeq (suc i) (suc j) x y = ifeq i j x y

DFA-hom : {n k : ℕ} → Mat n n (F k) → F 1 → Mat n n (F k)
DFA-hom _ Zero _ _ = Zero
DFA-hom _ (K A) i j = ifeq i j (K A) Zero
DFA-hom trans (X _) = trans
DFA-hom trans (f ⊕ g) = matSum _⊕_ (DFA-hom trans f) (DFA-hom trans g)
DFA-hom trans (f ⊗ g) = matProd _⊕_ Zero _⊗_ (DFA-hom trans f) (DFA-hom trans g)

module 2-deriv where
    -- transition matrix for derivative
    trans-2-deriv : Mat 2 2 (F 2)
    trans-2-deriv = mkMat ( ( X zero ∷ X (suc zero) ∷ [] )
                            ∷ ( Zero   ∷ X zero       ∷ [] )
                            ∷ []
                            )

    ∂ : F 1 → F 2
    ∂ f = DFA-hom trans-2-deriv f zero (suc zero)

    ∂X² : Set → Set
    ∂X² A = ⟦ ∂ (X₀ ⊗ X₀) ⟧′ A ⊤

      -- ∂X² ℕ = ℕ × ⊤ ⊎ ⊤ × ℕ ⊎ ⊥
      -- It works!

module 2-dissect where
    trans-2-dissect : Mat 2 2 (F 3)
    trans-2-dissect = mkMat ( ( X zero ∷ X (suc (suc zero)) ∷ [] )
                            ∷ ( Zero   ∷ X (suc zero)       ∷ [] )
                            ∷ []
                            )

    Δ : F 1 → F 3
    Δ f = DFA-hom trans-2-dissect f zero (suc zero)

    ΔX² : Set → Set → Set
    ΔX² B A = ⟦ Δ (X₀ ⊗ X₀) ⟧′ B A ⊤

-- Next step: can we express something like 'right' generically, for
-- n-dissection?

-- General transition matrix for n-dissection.
--
-- [ X_0 X_{n+1}   0       0     ...
-- [  0   X_1    X_{n+1}   0     ...
-- [  0    0      X_2    X_{n+1}  ...
-- [  0    0       0       X_3    ....
--
--  etc.
trans-n-dissect : (n : ℕ) → Mat n n (F (suc n))
trans-n-dissect zero () ()
trans-n-dissect (suc _) zero zero = X zero
trans-n-dissect (suc n) zero (suc j) = X (fromℕ (suc n))
trans-n-dissect (suc _) (suc _) zero = Zero
trans-n-dissect (suc n) (suc i) (suc j) = mapMat sucX (trans-n-dissect n) i j

D : (n : ℕ) → F 1 → Mat n n (F (suc n))
D n = DFA-hom (trans-n-dissect n)

_⋆ : {n : ℕ} → Fin n → Fin (suc n)
_⋆ = raise 1

right : {n : ℕ} {i j : Fin n} → (f : F 1)
      → ((D (suc n) f (i ⋆) (suc j) ⊗ X (suc j ⋆)) ⊕ D (suc n) f (i ⋆) (j ⋆))
         ≅
         (D (suc n) f (suc i) (suc j) ⊕ (X (i ⋆ ⋆) ⊗ D (suc n) f (i ⋆) (suc j)))
right Zero As = {!!}
right (K A) As = {!!}
right (X i) As = {!!}
right (f ⊕ g) As = {!!}
right (f ⊗ g) As = {!!}
-- Oh goodness.  The type typechecks. Now what?

-- ugghhhhh
lemma1 : {ℓ : Level} {A : Set ℓ} → (⊥ × A) ↔ ⊥
lemma1 = record { to = record { _⟨$⟩_ = proj₁ ; cong = {!!} } ; from = record { _⟨$⟩_ = λ () ; cong = {!!} } ; inverse-of = record { left-inverse-of = λ x → {!!} ; right-inverse-of = {!!} } }
