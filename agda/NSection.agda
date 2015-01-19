module NSection where

open import Data.Empty
open import Data.Unit
open import Data.Sum     hiding (map)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Fin
open import Data.Vec     hiding (map)

open import Function

open import Relation.Binary.PropositionalEquality hiding ( [_] )

open import Level using (Level)

-- Some utilities.

data SnocVecView {τ : Set₁} : {n : ℕ} → Vec τ n → Set₁ where
  NilV  : SnocVecView []
  SnocV : {n : ℕ} → (xs : Vec τ n) → (x : τ) → SnocVecView (xs ++ [ x ])

view : {τ : Set₁} {n : ℕ} → (v : Vec τ n) → SnocVecView v
view [] = NilV
view (x ∷ v)                with view v
view (x ∷ .[])              | NilV = SnocV [] x
view (x₁ ∷ .(xs ++ x ∷ [])) | SnocV xs x = SnocV (x₁ ∷ xs) x

-- Universe/algebra of n-ary functors.
data F : ℕ → Set₁ where
  Zero : {n : ℕ} → F n                -- void
  K    : {n : ℕ} → Set → F n          -- const
  X    : {n : ℕ} → Fin n → F n        -- projection, i.e. Id
  _⊕_  : {n : ℕ} → F n → F n → F n    -- sum
  _⊗_  : {n : ℕ} → F n → F n → F n    -- product
  L    : {n : ℕ} → F 1 → F (suc n)    -- "all clowns", i.e. (C F) A_0 ... A_n = F A_0
  R    : {n : ℕ} → F 1 → F (suc n)    -- "all jokers", i.e. (J F) A_0 ... A_n = F A_n

  -- Can't do least fixed point because it makes Agda unhappy, and I don't
  -- want to move to full-fledged containers right now
  -- μ    : {n : ℕ} → Fin (suc n) → F n

infixl 6 _⊕_
infixl 7 _⊗_

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
⟦_⟧ (L f) As = ⟦ f ⟧ [ head As ]
⟦_⟧ (R f) (A ∷ As) with view As
⟦_⟧ (R f) (A ∷ .[]) | NilV = ⟦ f ⟧ [ A ]
⟦_⟧ (R f) (A ∷ .(As′ ++ A′ ∷ [])) | SnocV As′ A′ = ⟦ f ⟧ [ A′ ]

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
map {As = A ∷ _} {B ∷ _} (L f) (A→B , _) fAs = map f (A→B , tt) fAs
-- map {As = A ∷ As} {Bs = B ∷ Bs} (R f) m fAs with view As | view Bs
-- map {.(suc 0)} {A ∷ .[]} {B ∷ .[]} (R f) m fAs | NilV | NilV = {!!}
-- map {._} {A ∷ .(As′ ++ A′ ∷ [])} {B ∷ .(Bs′ ++ B′ ∷ [])} (R f) m fAs | SnocV As′ A′ | SnocV Bs′ B′ = {!!}
map (R f) = {!!}

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
pres-id {As = A ∷ _} (L f) = pres-id f
-- pres-id {As = A ∷ As} (R f) with view As
-- ... | q = ?
pres-id (R f) = {!!}

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
pres-∘ {As = A ∷ _} {Bs = B ∷ _} {Cs = C ∷ _} (L f) = pres-∘ f
pres-∘ (R f) = {!!}

pres-∘-ext : ∀ {n : ℕ} {As Bs Cs : Vec Set n} → (f : F n)
       → {g : Map As Bs} → {h : Map Bs Cs} → {fAs : ⟦ f ⟧ As}
       → map f h ∘ map f g ≡ map f (Comp h g)
pres-∘-ext f = ext (pres-∘ f)

------------------------------------------------------------
-- Dissection
------------------------------------------------------------

-- Start with basic 2-dissection, as in Jokers & Clowns paper

D₂ : F 1 → F 2
D₂ Zero = Zero
D₂ (K _) = Zero
D₂ (X _) = One
D₂ (f ⊕ g) = D₂ f ⊕ D₂ g
D₂ (f ⊗ g) = (D₂ f ⊗ R g) ⊕ (L f ⊗ D₂ g)
D₂ (L f) = D₂ f
D₂ (R f) = D₂ f

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

⊕f : (f g : F 1) {j c : Set} → (j × ⟦ D₂ f ⟧′ c j) ⊎ ⟦ f ⟧′ c → (j × ⟦ D₂ (f ⊕ g) ⟧′ c j) ⊎ ⟦ f ⊕ g ⟧′ c
⊕f _ _ (inj₁ (j , f'cj)) = inj₁ (j , inj₁ f'cj)
⊕f _ _ (inj₂ fc) = inj₂ (inj₁ fc)

⊕g : (f g : F 1) {j c : Set} → (j × ⟦ D₂ g ⟧′ c j) ⊎ ⟦ g ⟧′ c → (j × ⟦ D₂ (f ⊕ g) ⟧′ c j) ⊎ ⟦ f ⊕ g ⟧′ c
⊕g _ _ (inj₁ (j , g'cj)) = inj₁ (j , inj₂ g'cj)
⊕g _ _ (inj₂ gc) = inj₂ (inj₂ gc)

mutual
  ⊗f : (f g : F 1) {j c : Set} → (j × ⟦ D₂ f ⟧′ c j) ⊎ ⟦ f ⟧′ c → ⟦ g ⟧′ j → (j × ⟦ D₂ (f ⊗ g) ⟧′ c j) ⊎ ⟦ f ⊗ g ⟧′ c
  ⊗f f g (inj₁ (j , f'cj)) gj = inj₁ (j , (inj₁ (f'cj , gj)))
  ⊗f f g (inj₂ fc) gj = ⊗g f g fc (right g (inj₁ gj))

  ⊗g : (f g : F 1) {j c : Set} → ⟦ f ⟧′ c → (j × ⟦ D₂ g ⟧′ c j) ⊎ ⟦ g ⟧′ c → (j × ⟦ D₂ (f ⊗ g) ⟧′ c j) ⊎ ⟦ f ⊗ g ⟧′ c
  ⊗g f g fc (inj₁ (j , g'cj)) = inj₁ (j , (inj₂ (fc , g'cj)))
  ⊗g f g fc (inj₂ gc) = inj₂ (fc , gc)

  right : (f : F 1) → {j c : Set} → (⟦ f ⟧′ j ⊎ (⟦ D₂ f ⟧′ c j × c)) → ((j × ⟦ D₂ f ⟧′ c j) ⊎ ⟦ f ⟧′ c)
  right Zero (inj₁ ())
  right Zero (inj₂ (() , _))
  right (K A) (inj₁ a) = inj₂ a
  right (K A) (inj₂ (() , _))
  right (X zero) (inj₁ j) = inj₁ (j , tt)
  right (X (suc ()))
  right (X zero) (inj₂ (tt , c)) = inj₂ c
  right (f ⊕ g) (inj₁ (inj₁ fj)) = ⊕f f g (right f (inj₁ fj))
  right (f ⊕ g) (inj₁ (inj₂ gj)) = ⊕g f g (right g (inj₁ gj))
  right (f ⊕ g) (inj₂ (inj₁ f'cj , c)) = ⊕f f g (right f (inj₂ (f'cj , c)))
  right (f ⊕ g) (inj₂ (inj₂ g'cj , c)) = ⊕g f g (right g (inj₂ (g'cj , c)))
  right (f ⊗ g) (inj₁ (fj , gj)) = ⊗f f g (right f (inj₁ fj)) gj
  right (f ⊗ g) (inj₂ (inj₁ (f'cj , gj) , c)) = ⊗f f g (right f (inj₂ (f'cj , c))) gj
  right (f ⊗ g) (inj₂ (inj₂ (fc , g'cj) , c)) = ⊗g f g fc (right g (inj₂ (g'cj , c)))
  right (L f) x = right f x
  right (R f) x = right f x

-- Next: try making types for pointed dissections?  Or go ahead and try generalizing to n-section?


------------------------------------------------------------
-- Generalized n-dissection
------------------------------------------------------------

record Semiring {ℓ : Level} (A : Set ℓ) : Set ℓ where
  field _⊞_ : A → A → A
  field id⊞ : A
  field _⊡_ : A → A → A
  field id⊡ : A

open Semiring {{...}}

-- instance 
--   VecSemiring : {ℓ : Level} {A : Set ℓ} {n : ℕ} {{Semiring A}} → Semiring (Vec A n)
--   VecSemiring = ?

-- Matrices
vecSum : {ℓ : Level} {n : ℕ} {A : Set ℓ} → (A → A → A) → Vec A n → Vec A n → Vec A n
vecSum = zipWith

dot : {ℓ : Level} {n : ℕ} {A : Set ℓ} → (A → A → A) → (A → A → A) → Vec A n → Vec A n → Vec A n
dot _⊞_ _⊡_ v₁ v₂ = {!!} -- zipWith _⊡_ v₁ v₂

-- M : {ℓ : Laevel} → ℕ → ℕ → Set ℓ → Set ℓ
-- M m n A = Fin m → Fin n → A

-- row : {ℓ : Level} {m n : ℕ} {A : Set ℓ} → Fin m → M m n A → Vec A n
-- row i m = m i

-- col : {ℓ : Level} {m n : ℕ} {A : Set ℓ} → Fin n → M m n A → Vec A m
-- col j m = λ i → m i j

-- matSum : {ℓ : Level} {m n : ℕ} {A : Set ℓ} → (A → A → A) → M m n A → M m n A → M m n A
-- matSum _⊞_ m₁ m₂ = λ i j → m₁ i j ⊞ m₂ i j

-- matProd : {ℓ : Level} {m n p : ℕ} {A : Set ℓ} → (A → A → A) → (A → A → A)
--         → M m n A → M n p A → M m p A
-- matProd = {!!}

-- D : {n : ℕ} → F 1 → F (suc (suc n))
-- D Zero = Zero
-- D (K _) = Zero
-- D {zero} (X _) = One
-- D {_} (X _) = Zero
-- D (f ⊕ g) = D f ⊕ D g
-- D (f ⊗ g) = {!!}  -- hmm, this is the hard/interesting case!
-- D (L f) = D f
-- D (R f) = D f
