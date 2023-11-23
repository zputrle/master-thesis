open import Level

open import Data.Unit            using (tt) renaming (⊤ to T)
open import Data.Bool            using (Bool; true; false; not)
open import Data.Nat             using (ℕ ; suc; _≡ᵇ_; _<ᵇ_)
open import Data.Product         using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)


module _ where

--
-- We define Prop as defined in CIC.
--

record CICProp : Setω where

  infix  5 ⊢_

  field
    prop : Set zero
    ⊢_ : prop → Set zero

    all : {𝓁 : Level} (A : Set 𝓁) → (A → prop) → prop
    all-intro : {𝓁 : Level} {A : Set 𝓁} {P : A → prop} → ((x : A) → ⊢ P x) → ⊢ all _ P
    all-elim : {𝓁 : Level} {A : Set 𝓁} {P : A → prop} → (a : A) → ⊢ all _ P → ⊢ P a

--
-- Logic for Prop
--

module Logic (𝒫 : CICProp) where
  
  open CICProp 𝒫

  infixr 20 _⇒_

  _⇒_ : prop → prop → prop
  p ⇒ q = all (⊢ p) λ _ → q
  
  ⇒-intro : {p q : prop} → (⊢ p → ⊢ q) → ⊢ p ⇒ q
  ⇒-intro *p→*q = all-intro *p→*q
  
  ⇒-elim : {p q : prop} → ⊢ p ⇒ q → ⊢ p → ⊢ q
  ⇒-elim *p⇒*q *p = all-elim  *p *p⇒*q

  --
  -- Existential quantifier
  --
  
  ∃ : {𝓁 : Level} → {A : Set 𝓁} → (P : A → prop) → prop
  ∃ {_} {A} P = all prop (λ t → (all A (λ x → (P x) ⇒ t)) ⇒ t)
  
  ∃-intro : {𝓁 : Level} {A : Set 𝓁} → (a : A) → {P : A → prop} → ⊢ P a → ⊢ ∃ P
  ∃-intro a {P} *Pa = all-intro λ t → all-intro λ *allA → ⇒-elim (all-elim a *allA) *Pa
  
  ∃-elim : {𝓁 : Level} {A : Set 𝓁} {P : A → prop} {Q : prop} → ⊢ ∃ P → ((a : A) → ⊢ P a → ⊢ Q) → ⊢ Q
  ∃-elim {_} {A} {P} {Q} *∃P p = all-elim (all-intro λ x → ⇒-intro (p x)) (all-elim Q *∃P)

  --
  -- Truth
  --
  
  ⊤ : prop
  ⊤ = all prop λ p → (p ⇒ p)

  ⊤-intro : ⊢ ⊤
  ⊤-intro = all-intro λ p → ⇒-intro λ pp → pp

  --
  -- Falsehood
  --

  ⊥ : prop
  ⊥ = all prop (λ p → p)
  
  ⊥-elim : {p : prop} → ⊢ ⊥ → ⊢ p
  ⊥-elim {p} d = all-elim p d

  --
  -- Or
  --

  infixr 30 _∨_

  _∨_ : prop → prop → prop
  p ∨ q = all prop (λ r → (p ⇒ r) ⇒ (q ⇒ r) ⇒ r)  

  ∨-intro-left : {p q : prop} → ⊢ p → ⊢ p ∨ q
  ∨-intro-left {p} {q} *p = all-intro (λ x → ⇒-intro (λ *p→x → ⇒-intro (λ _ → ⇒-elim *p→x *p)))

  ∨-intro-right : {p q : prop} → ⊢ q → ⊢ p ∨ q
  ∨-intro-right {p} {q} *q = all-intro (λ x → ⇒-intro (λ *p→x → ⇒-intro (λ *q→x → ⇒-elim *q→x *q)))

  ∨-elim : {p q r : prop} → (⊢ p → ⊢ r) → (⊢ q → ⊢ r) → ⊢ p ∨ q → ⊢ r
  ∨-elim {p} {q} {r} *p→*r *q→*r *p∨q = ⇒-elim (⇒-elim elim-*p∨q (⇒-intro *p→*r)) (⇒-intro *q→*r)
    where
      elim-*p∨q : ⊢ (p ⇒ r) ⇒ (q ⇒ r) ⇒ r
      elim-*p∨q = all-elim r *p∨q
    
  --
  -- And
  --

  infixr 30 _∧_

  _∧_ : prop → prop → prop
  p ∧ q = all prop λ r → ((p ⇒ (q ⇒ r)) ⇒ r)

  ∧-intro : {p q : prop} → ⊢ p → ⊢ q → ⊢ p ∧ q
  ∧-intro {p} {q} *p *q = all-intro λ x → ⇒-intro λ *p⇒q⇒x -> ⇒-elim (⇒-elim *p⇒q⇒x *p) *q

  ∧-elim-left : {p q : prop} → ⊢ p ∧ q → ⊢ p
  ∧-elim-left {p} {q} *p∧q = ⇒-elim (all-elim p *p∧q) (⇒-intro λ *p → ⇒-intro λ _ → *p)

  ∧-elim-right : {p q : prop} → ⊢ p ∧ q → ⊢ q
  ∧-elim-right {p} {q} *p∧q = ⇒-elim (all-elim q *p∧q) (⇒-intro λ _ → ⇒-intro λ *q → *q)

  --
  -- Not
  --

  infix 40 ¬_

  ¬_ : prop → prop
  ¬ p = p ⇒ ⊥

  ¬-intro : {p : prop} → (⊢ p → ⊢ ⊥) → ⊢ ¬ p
  ¬-intro = ⇒-intro

  ¬-elim : {p : prop} → ⊢ ¬ p → ⊢ p → ⊢ ⊥ 
  ¬-elim = ⇒-elim

  --
  -- Mapping from Bool to prop.
  --

  E : Bool → prop
  E true = ⊤
  E false = ⊥

  --
  -- Decidable equality for Bool
  --

  infix 50 _==𝔹_

  _==𝔹_ : Bool → Bool → prop
  x ==𝔹 y = E (eq x y)
    where 
      eq : Bool → Bool → Bool
      eq false false = true
      eq false true = false
      eq true false = false
      eq true true = true

  --
  -- Decidable equality for ℕ
  --

  infix 50 _==ℕ_

  _==ℕ_ : ℕ → ℕ → prop
  x ==ℕ y = E (x ≡ᵇ y)
  
  infix 50 _==ℕ'_

  _==ℕ'_ : Maybe ℕ → Maybe ℕ → prop
  just x ==ℕ' just y =  x ==ℕ y
  just x ==ℕ' nothing = ⊥
  nothing ==ℕ' _ = ⊥

  --
  -- Decidable greater or equal for ℕ
  --

  infix 50 _≥ℕ_

  _≥ℕ_ : ℕ → ℕ → prop
  x ≥ℕ y = E (not (x <ᵇ y))

  _≥ℕ'_ : Maybe ℕ → Maybe ℕ → prop
  just x ≥ℕ' just y = x ≥ℕ y
  just x ≥ℕ' nothing = ⊥
  nothing ≥ℕ' _ = ⊥
 
  --
  -- Some useful lemmas
  --

  ¬¬-intro : {A : prop} → ⊢ A → ⊢ ¬ ¬ A
  ¬¬-intro *a = ¬-intro λ *¬a → ¬-elim *¬a *a

  ¬¬¬-elim : {A : prop} → ⊢ ¬ ¬ ¬ A → ⊢ ¬ A
  ¬¬¬-elim *¬¬¬x = ⇒-intro (λ *a → ⇒-elim *¬¬¬x (¬¬-intro *a))


module _ (𝒫 : CICProp) where

  open CICProp 𝒫
  open Logic 𝒫

  --
  -- We define a new universe of proposition where every proposition is stable and call it CICProp¬¬.
  --

  record prop¬¬ : Set where

    infix 10 `_

    field
      `_ : prop
      stable : ⊢ ¬ ¬ (`_) → ⊢ (`_)

  open prop¬¬

  CICProp¬¬ : CICProp
  CICProp¬¬ = record {
  
    prop = prop¬¬ ;
    ⊢_ = λ { record { `_ = p ; stable = s } → ⊢ p} ;
        
    all = λ A P → record {
      `_ = all A λ a → ` P a ;
      stable = λ t → all-intro
        λ a → stable (P a) (⇒-intro (λ *¬Pa →
          ⇒-elim t (⇒-intro (λ h → ⇒-elim *¬Pa (all-elim a h))))) } ;
    all-intro = all-intro ;
    all-elim = all-elim }

  --
  -- Logic for CICProp¬¬.
  --

  module Logicₙ (𝓅ₙ : prop¬¬) where

    open prop¬¬ 𝓅ₙ

    --
    -- Implication
    --

    _⇒ₙ_ : prop¬¬ → prop¬¬ → prop¬¬
    p ⇒ₙ q = record {
      `_ = (` p) ⇒ (` q) ;
      stable = λ *¬¬p→q → ⇒-intro ( λ *p → stable q
        (¬-intro λ ¬*q → ⇒-elim *¬¬p→q
          (¬-intro (λ *p→q → ⇒-elim ¬*q  (⇒-elim *p→q *p)))))}

    -- TODO: Add rules for introduction and elimination of => even if they are the same. Do the same for exists, falsehood and truth.

    --
    -- Existential quantifier
    --

    ∃ₙ : {𝓁 : Level} {A : Set 𝓁} → (A → prop¬¬) → prop¬¬
    ∃ₙ P = record {
      `_ = ¬ ¬ (∃ (λ a → ` P a)) ;
      stable = λ t → ¬¬¬-elim t }
    ∃ₙ-intro : {𝓁 : Level} {A : Set 𝓁} → (a : A) → {P : A → prop¬¬} → ⊢ ` P a → ⊢ ` ∃ₙ P
    ∃ₙ-intro {_} {A} a {P} *Pa =
      ¬-intro λ *¬∃aP → ⇒-elim *¬∃aP
        (∃-intro {_} {_} a {λ a → ` (P a)} *Pa)
    ∃ₙ-elim : {𝓁 : Level} {A : Set 𝓁} {P : A → prop¬¬} {Q : prop¬¬} → ⊢ ` ∃ₙ P → ((a : A) → ⊢ ` P a → ⊢ ` Q) → ⊢ ` Q
    ∃ₙ-elim {_} {_} {_} {Q} *¬¬∃Pa p =
       stable Q (¬-intro λ *¬Q →
         ¬-elim *¬¬∃Pa (¬-intro (λ *∃Pa →
           ∃-elim *∃Pa λ a *Pa → ⇒-elim *¬Q (p a *Pa))))

    --
    -- Truth
    --

    ⊤ₙ : prop¬¬
    ⊤ₙ = record {
      `_ = ⊤ ;
      stable = λ _ → ⊤-intro }

    --
    -- Falsehood
    --

    ⊥ₙ : prop¬¬
    ⊥ₙ = record {
      `_ = ⊥ ;
      stable = λ *¬¬⊥ → ⇒-elim *¬¬⊥ (⇒-intro λ *⊥ → *⊥) }

    --
    -- Or
    --

    infix 30 _∨ₙ_

    _∨ₙ_ : prop¬¬ → prop¬¬ → prop¬¬
    p ∨ₙ q = record {
      `_ = ¬ ¬ ((` p) ∨ (` q)) ;
      stable = λ t → ¬¬¬-elim t }
   
    ∨ₙ-intro-left :  {p q : prop¬¬} → ⊢ ` p → ⊢ ` (p ∨ₙ q)
    ∨ₙ-intro-left *p = ¬-intro (λ *¬p∨q → ⇒-elim *¬p∨q (∨-intro-left *p))

    ∨ₙ-intro-right : {p q : prop¬¬} → ⊢ ` q → ⊢ ` (p ∨ₙ q)
    ∨ₙ-intro-right *q = ¬-intro (λ *¬p∨q → ⇒-elim *¬p∨q (∨-intro-right *q))

    ∨ₙ-elim : {p q r : prop¬¬} →
                 (⊢ ` p → ⊢ ` r) →
                 (⊢ ` q → ⊢ ` r) →
                   ⊢ ` (p ∨ₙ q) → ⊢ ` r
    ∨ₙ-elim {p} {q} {r} *p→*r *q→*r *¬¬p∨q = stable r (¬-intro (λ *¬r → ¬-elim *¬¬p∨q (
      ¬-intro λ *p∨q → ∨-elim
        (λ *p → ⇒-elim *¬r (*p→*r *p))
        (λ *q → ⇒-elim *¬r (*q→*r *q))
        *p∨q)))


    --
    -- And
    --

    infix 30 _∧ₙ_
    _∧ₙ_ : prop¬¬ → prop¬¬ → prop¬¬
    p ∧ₙ q = record {
        `_ = ¬ ¬ ((` p) ∧ (` q)) ;
        stable = λ t → ¬¬¬-elim t }

    ∧ₙ-intro : {p q : prop¬¬} → ⊢ ` p → ⊢ ` q → ⊢ ` (p ∧ₙ q)
    ∧ₙ-intro {p} {q} *p *q = ¬-intro λ ¬p∧q → ¬-elim ¬p∧q (∧-intro *p *q)

    ∧ₙ-elim-left : {p q : prop¬¬} → ⊢ ` (p ∧ₙ q) → ⊢ ` p
    ∧ₙ-elim-left {p} {q} *¬¬p∧q = stable p (¬-intro λ ¬p → ¬-elim *¬¬p∧q
      (¬-intro λ p∧q  → ¬-elim ¬p  (∧-elim-left p∧q)))

    ∧ₙ-elim-right : {p q : prop¬¬} → ⊢ ` (p ∧ₙ q) → ⊢ ` q
    ∧ₙ-elim-right {p} {q} *¬¬p∧q = stable q (¬-intro λ ¬q → ¬-elim *¬¬p∧q
      (¬-intro λ p∧q  → ¬-elim ¬q  (∧-elim-right p∧q)))

    --
    -- Negation
    --

    infix 40 ¬ₙ_
    
    ¬ₙ_ : prop¬¬ → prop¬¬
    ¬ₙ p = record {
      `_ = ¬ (` p) ;
      stable = λ *¬¬¬p → ¬¬¬-elim *¬¬¬p }

    ¬ₙ-intro : {p : prop¬¬} → (⊢ ` p → ⊢ ` ⊥ₙ) → ⊢ ` (¬ₙ p)
    ¬ₙ-intro = ¬-intro

    ¬ₙ-elim : {p : prop¬¬} → ⊢ ` (¬ₙ p) → ⊢ ` p → ⊢ ` ⊥ₙ
    ¬ₙ-elim = ¬-elim

    --
    -- Decidable equality for ℕ
    --

    infix 50 _==ℕₙ_

    _==ℕₙ_ : ℕ → ℕ → prop¬¬
    x ==ℕₙ y = record {
      `_ = x ==ℕ y ;
      stable = aux }
        where
          aux : ⊢ ¬ ¬ x ==ℕ y → ⊢ x ==ℕ y
          aux t with x ≡ᵇ y
          ... | false = ⇒-elim t (⇒-intro (λ Q → Q))
          ... | true = ⊤-intro

    infix 50 _==ℕₙ'_

    _==ℕₙ'_ : Maybe ℕ → Maybe ℕ → prop¬¬
    just x ==ℕₙ' just y = x ==ℕₙ y
    just x ==ℕₙ' nothing = ⊥ₙ
    nothing ==ℕₙ' y = ⊥ₙ

    --
    -- Decidable greater or equal for ℕ
    --
    
    infix 50 _≥ℕₙ_ 

    _≥ℕₙ_ : ℕ → ℕ → prop¬¬
    x ≥ℕₙ y = record {
      `_ = x ≥ℕ y ;
      stable = aux }
        where
          aux : ⊢ ¬ ¬ x ≥ℕ y → ⊢ x ≥ℕ y
          aux t with not (x <ᵇ y)
          ... | false = ⇒-elim t (⇒-intro (λ Q → Q))
          ... | true = ⊤-intro

    _≥ℕₙ'_ : Maybe ℕ → Maybe ℕ → prop¬¬
    just x ≥ℕₙ' just y = x ≥ℕₙ y
    just x ≥ℕₙ' nothing = ⊥ₙ
    nothing ≥ℕₙ' just y = ⊥ₙ
    nothing ≥ℕₙ' nothing = ⊥ₙ


    --
    -- Decidable equality for Bool
    --

    infix 50 _==𝔹ₙ_

    _==𝔹ₙ_ : Bool → Bool → prop¬¬
    false ==𝔹ₙ false = record { `_ = false ==𝔹 false ; stable = stable ⊤ₙ }
    false ==𝔹ₙ true  = record { `_ = false ==𝔹 true ; stable = stable ⊥ₙ }
    true  ==𝔹ₙ false = record { `_ = true ==𝔹 false ; stable = stable ⊥ₙ }
    true  ==𝔹ₙ true  = record { `_ = true ==𝔹 true  ; stable = stable ⊤ₙ }

    ==𝔹ₙ≡==𝔹 : {a b : Bool} → (` a ==𝔹ₙ b) ≡ (a ==𝔹 b)
    ==𝔹ₙ≡==𝔹 {false} {false} = refl
    ==𝔹ₙ≡==𝔹 {false} {true} = refl
    ==𝔹ₙ≡==𝔹 {true} {false} = refl
    ==𝔹ₙ≡==𝔹 {true} {true} = refl

  module _ (𝓅ₙ : prop¬¬) where
 
    open prop¬¬ 𝓅ₙ

    open CICProp CICProp¬¬
      hiding (prop; ⊢_)
      renaming (
        all to allₙ;
        all-intro to allₙ-intro;
        all-elim to allₙ-elim)

    open Logicₙ 𝓅ₙ

    --
    -- We check that prop¬¬ has the desired properties.
    --

    --
    --  LEM is valid in prop¬¬.
    --

    LEMₙ : {Q : prop¬¬} → ⊢ ` (Q ∨ₙ ¬ₙ Q)
    LEMₙ {Q} = ¬-intro (λ t → ¬-elim t
      (∨-intro-left (stable Q 
        (¬-intro (λ *¬Q →
         ⇒-elim t (∨-intro-right *¬Q))))))

    --
    --  SCT is preserved.
    --
    
    postulate SCT : Σ[ Φ ∈ (ℕ → ℕ → ℕ → Maybe ℕ) ]
                      ⊢ 
                        -- Is stable.
                        (all ℕ λ c → all ℕ λ x → all ℕ λ n₁ → all ℕ λ n₂ → all ℕ λ v → 
                          (Φ c x n₁ ==ℕ' just v) ⇒ (n₂ ≥ℕ n₁ ⇒ (Φ c x n₂ ==ℕ' just v))) ∧
                        -- CT holds.
                        (all (ℕ → ℕ → ℕ) λ f →
                          ∃ λ (γ : ℕ → ℕ) →
                            all ℕ λ i → all ℕ λ x → ∃ λ (n : ℕ) →
                              Φ (γ i) x n ==ℕ' just (f i n))

    -- First, we show stability of Φ is preserved.
    SCTₙ-STABLE : Σ[ Φ ∈ (ℕ → ℕ → ℕ → Maybe ℕ) ]
                      ⊢ ` allₙ ℕ λ c → allₙ ℕ λ x → allₙ ℕ λ n₁ → allₙ ℕ λ n₂ → allₙ ℕ λ v → 
                          (Φ c x n₁ ==ℕₙ' just v) ⇒ₙ (n₂ ≥ℕₙ n₁ ⇒ₙ (Φ c x n₂ ==ℕₙ' just v))
    SCTₙ-STABLE = (proj₁ SCT) ,
      (all-intro (λ c → all-intro (λ x → all-intro (λ n₁ → all-intro (λ n₂ → all-intro (λ v →
        ⇒-intro (λ eq-n₁ →
          ⇒-intro (λ n₂≥ℕₙn₁ →
            let t = all-elim v (all-elim n₂ (all-elim n₁ (all-elim x (all-elim c (∧-elim-left (proj₂ SCT))))))
              in
              areEq (proj₁ SCT) c x n₁ n₂ v eq-n₁ n₂≥ℕₙn₁ t))))))))
      where

        areEq : (Φ : ℕ → ℕ → ℕ →  Maybe ℕ) → (c : ℕ) → (x : ℕ) → (n₁ : ℕ) → (n₂ : ℕ) → (v : ℕ)
                  → ⊢ ` Φ c x n₁ ==ℕₙ' just v 
                  → ⊢ ` n₂ ≥ℕₙ n₁
                  → ⊢  Φ c x n₁ ==ℕ' just v ⇒ n₂ ≥ℕ n₁ ⇒ Φ c x n₂ ==ℕ' just v
                    → ⊢ ` Φ c x n₂ ==ℕₙ' just v
        areEq Φ c x n₁ n₂ v eq-n₁ n₂≥ℕₙn₁ t with Φ c x n₁ | Φ c x n₂
        ... | just y₁ | just y₂ = ⇒-elim (⇒-elim t eq-n₁) n₂≥ℕₙn₁       
        ... | nothing | just y₂ = ⇒-elim (⇒-elim t eq-n₁) n₂≥ℕₙn₁ 
        ... | just y₁ | nothing = ⇒-elim (⇒-elim t eq-n₁) n₂≥ℕₙn₁
        ... | nothing | nothing = ⇒-elim (⇒-elim t eq-n₁) n₂≥ℕₙn₁
        
    -- Second, we show that CT is preserved.
    SCTₙ-CT : Σ[ Φ ∈ (ℕ → ℕ → ℕ → Maybe ℕ) ]
              ⊢ ` allₙ (ℕ → ℕ → ℕ) λ f →
                ∃ₙ λ (γ : ℕ → ℕ) →
                  allₙ ℕ λ i → allₙ ℕ λ x → ∃ₙ λ (n : ℕ) →
                    Φ (γ i) x n ==ℕₙ' just (f i n)
    SCTₙ-CT =
      proj₁ SCT , all-intro λ f → 
        ∃-elim  (all-elim f (∧-elim-right (proj₂ SCT))) (λ γ p →  ¬-intro λ t → ⇒-elim t 
          (∃-intro γ
            (all-intro λ i → all-intro (λ x →
              ∃-elim ((all-elim x (all-elim i p)))
                λ n p' → ¬-intro λ t' → ⇒-elim t'
                  (∃-intro n
                   (areEq (proj₁ SCT) f γ i x n p'))))))

      where

        areEq :(Φ : ℕ → ℕ → ℕ →  Maybe ℕ) → (f : ℕ → ℕ → ℕ) →
                  (γ : ℕ → ℕ) → (i : ℕ) → (x : ℕ) → (n : ℕ) →
                    ⊢ Φ (γ i) x n ==ℕ' just (f i n) →
                      ⊢ ` (Φ (γ i) x n ==ℕₙ' just (f i n))
        areEq Φ f γ i x n eq with Φ (γ i) x n 
        ... | just x₁ = eq
        ... | nothing = eq

    -- Third, we show that SCTₙ by using SCTₙ-STABLE and SCTₙ-CT.
    SCTₙ : Σ[ Φ ∈ (ℕ → ℕ → ℕ → Maybe ℕ) ]
              ⊢ ` (allₙ ℕ λ c → allₙ ℕ λ x → allₙ ℕ λ n₁ → allₙ ℕ λ n₂ → allₙ ℕ λ v → 
                    (Φ c x n₁ ==ℕₙ' just v) ⇒ₙ (n₂ ≥ℕₙ n₁ ⇒ₙ (Φ c x n₂ ==ℕₙ' just v))) ∧ₙ
                  (allₙ (ℕ → ℕ → ℕ) λ f →
                    ∃ₙ λ (γ : ℕ → ℕ) →
                      allₙ ℕ λ i → allₙ ℕ λ x → ∃ₙ λ (n : ℕ) →
                        Φ (γ i) x n ==ℕₙ' just (f i n))
    SCTₙ = proj₁ SCT , ∧ₙ-intro
      {allₙ ℕ λ c → allₙ ℕ λ x → allₙ ℕ λ n₁ → allₙ ℕ λ n₂ → allₙ ℕ λ v → 
        ((proj₁ SCT) c x n₁ ==ℕₙ' just v) ⇒ₙ (n₂ ≥ℕₙ n₁ ⇒ₙ ((proj₁ SCT) c x n₂ ==ℕₙ' just v))}
      {allₙ (ℕ → ℕ → ℕ) λ f →
        ∃ₙ λ (γ : ℕ → ℕ) →
          allₙ ℕ λ i → allₙ ℕ λ x → ∃ₙ λ (n : ℕ) →
            (proj₁ SCT) (γ i) x n ==ℕₙ' just (f i n)}
        (proj₂ SCTₙ-STABLE) (proj₂ SCTₙ-CT)

    --
    -- MP is preserved.
    --

    postulate MP  : {𝓁 : Level} → {A : Set 𝓁} → (P : A → prop) → ⊢ ¬ ¬ ∃ P →  ⊢ ∃ P

    postulate MPₙ : {𝓁 : Level} → {A : Set 𝓁} → (P : A → prop¬¬) → ⊢ ` ¬ₙ ¬ₙ ∃ₙ P → ⊢ ` ∃ₙ P

    postulate MPˢ  : {𝓁 : Level} → {A : Set 𝓁} → (P : A → prop) → ⊢ ¬ ¬ ∃ P → Σ[ a ∈ A ] ⊢ P a

    MPˢₙ : {𝓁 : Level} → {A : Set 𝓁} → (P : A → prop¬¬) → ⊢ ` ¬ₙ ¬ₙ ∃ₙ P → Σ[ a ∈ A ] ⊢ ` P a
    MPˢₙ P' p = (MPˢ (λ x → ` P' x)) (¬¬¬-elim p)

    --
    -- Large elimination of ⊥ is preserved.
    --

    postulate LE⊥ : {𝓁 : Level} → {A : Set 𝓁} → ⊢ ⊥ → A

    LE⊥ₙ : {𝓁 : Level} → {A : Set 𝓁} → ⊢ ` ⊥ₙ → A
    LE⊥ₙ p = LE⊥ p

    --
    -- Large elimination on equality is preserved.
    --

    postulate LE≡ : {𝓁₁ 𝓁₂ : Level} → {X : Set 𝓁₁} → (A : X → Set 𝓁₂) → (x₁ x₂ : X) → x₁ ≡ x₂ → A x₁ → A x₂
    
    LE≡ₙ : {𝓁₁ 𝓁₂ : Level} → {X : Set 𝓁₁} → (A : X → Set 𝓁₂) → (x₁ x₂ : X) → x₁ ≡ x₂ → A x₁ → A x₂
    LE≡ₙ = LE≡

    --
    -- Large elimination for existential quantification over decidable predicates on natural numbers is preserved.
    --

    -- We can get LE∃Pℕₙ from MPˢₙ.
    
    LE∃Pℕₙ' : (f : ℕ → Bool) → ⊢ ` (∃ₙ (λ (n : ℕ) → (f n) ==𝔹ₙ true)) → Σ[ n ∈ ℕ ] ⊢ ` (f n) ==𝔹ₙ true
    LE∃Pℕₙ' f x = MPˢₙ (λ x → f x ==𝔹ₙ true) (¬¬-intro x)

    -- We can get LE∀Pℕₙ from LE∃Pℕ.

    postulate LE∃Pℕ : (f : ℕ → Bool) → ⊢ ∃ (λ (n : ℕ) → (f n) ==𝔹 true) → Σ[ n ∈ ℕ ] ⊢ (f n) ==𝔹 true

    postulate funext : {X : Set} {Y : X → Set} (f g : (x : X ) → Y x) → ((x : X) → f x ≡ g x) → f ≡ g

    LE∃Pℕₙ : (f : ℕ → Bool) → ⊢ ` (∃ₙ (λ (n : ℕ) → (f n) ==𝔹ₙ true)) → Σ[ n ∈ ℕ ] ⊢ ` (f n) ==𝔹ₙ true
    LE∃Pℕₙ f p =
      proj₁ sg ,
      subst (λ e → ⊢ e) (sym (==𝔹ₙ≡==𝔹 {f (proj₁ sg)} {true})) (proj₂ sg)
        where
          sg : Σ ℕ (λ z → ⊢ (f z ==𝔹 true))
          sg = (LE∃Pℕ f (MP (λ (n : ℕ) → (f n) ==𝔹 true)
            (subst (λ f → ⊢ ¬ ¬ ∃ f)
              (funext (λ n → ` f n ==𝔹ₙ true) (λ n → f n ==𝔹 true) λ n → ==𝔹ₙ≡==𝔹 {f n} {true}) p)))

    --
    -- prop¬¬ is consistent.
    --

    prop¬¬IsConsistent : (⊢ ` ⊥ₙ) → (⊢ ⊥) 
    prop¬¬IsConsistent = λ x → x
        
