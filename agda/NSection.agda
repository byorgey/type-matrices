module NSection where

open import Data.Empty
open import Data.Unit
open import Data.Sum     hiding (map)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Fin
open import Data.Vec     hiding (map)

open import Function

open import Relation.Binary.PropositionalEquality

-- Universe/algebra of n-ary functors.
data F : ℕ → Set₁ where
  Zero : {n : ℕ} → F n                -- void
  K    : {n : ℕ} → Set → F n          -- const
  X    : {n : ℕ} → Fin n → F n        -- projection, i.e. Id
  _⊕_  : {n : ℕ} → F n → F n → F n    -- sum
  _⊗_  : {n : ℕ} → F n → F n → F n    -- product

  -- Can't do least fixed point because it makes Agda unhappy, and I don't
  -- want to move to full-fledged containers right now

-- One is a synonym for the constantly ⊤ functor
One : ∀ {n} → F n
One = K ⊤

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
