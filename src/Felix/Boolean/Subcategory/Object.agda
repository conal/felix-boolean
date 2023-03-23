-- *Full* subcategory or something like it.
{-# OPTIONS --safe --without-K #-}

open import Level using (Level)

open import Felix.Raw
open import Felix.Homomorphism

module Felix.Boolean.Subcategory.Object
  {j} (J : Set j)
  {o ℓ} {obj : Set o}
  (_↠_ : obj → obj → Set ℓ) (let infix 0 _↠_; _↠_ = _↠_)
  ⦃ cat : Category _↠_ ⦄
  ⦃ Hₒ : Homomorphismₒ J obj ⦄
 where

-- import Felix.Laws as L
-- open import Felix.Reasoning

open import Felix.Boolean
open import Felix.Boolean.Homomorphism
open import Felix.Subcategory.Object J _↠_

module boolean-subcategory-instances where instance

  subcat-logic : ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
                 ⦃ _ : Cartesian _↠_ ⦄ ⦃ _ : Logic _↠_ ⦄
                 ⦃ _ : Products J ⦄  ⦃ _ : Boolean J ⦄ ⦃ _ : ProductsH J _↠_ ⦄
                 ⦃ _ : BooleanH J _↠_ ⦄
               → Logic _⇨_
  subcat-logic = record
    { false = mk (β ∘ false ∘ ε⁻¹)
    ; true  = mk (β ∘ true  ∘ ε⁻¹)
    ; not   = mk (β ∘ not ∘ β⁻¹)
    ; nand  = mk (β ∘ nand ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
    ; nor   = mk (β ∘ nor  ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
    ; xor   = mk (β ∘ xor  ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
    }
