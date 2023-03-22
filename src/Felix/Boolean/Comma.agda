{-# OPTIONS --safe --without-K #-}

open import Felix.Raw
open import Felix.Equiv
open import Felix.Laws as L
       hiding (Category; Cartesian; CartesianClosed) -- ; Logic; Monoid
open import Felix.Homomorphism
open ≈-Reasoning
open import Felix.Reasoning

module Felix.Boolean.Comma
   {o₀}{obj₀ : Set o₀} {ℓ₀} (_⇨₀_ : obj₀ → obj₀ → Set ℓ₀) ⦃ _ : Category _⇨₀_ ⦄
   {o₁}{obj₁ : Set o₁} {ℓ₁} (_⇨₁_ : obj₁ → obj₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄
   {o₂}{obj₂ : Set o₂} {ℓ₂} (_⇨₂_ : obj₂ → obj₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄
   {q₀} ⦃ _ : Equivalent q₀ _⇨₀_ ⦄ ⦃ _ : L.Category _⇨₀_ ⦄
   {q₁} ⦃ _ : Equivalent q₁ _⇨₁_ ⦄ -- ⦃ _ : L.Category _⇨₁_ ⦄
   {q₂} ⦃ _ : Equivalent q₂ _⇨₂_ ⦄ -- ⦃ _ : L.Category _⇨₂_ ⦄
   ⦃ hₒ₁ : Homomorphismₒ obj₁ obj₀ ⦄ ⦃ h₁ : Homomorphism _⇨₁_ _⇨₀_ ⦄
     ⦃ catH₁ : CategoryH _⇨₁_ _⇨₀_ ⦄
   ⦃ hₒ₂ : Homomorphismₒ obj₂ obj₀ ⦄ ⦃ h₂ : Homomorphism _⇨₂_ _⇨₀_ ⦄
     ⦃ catH₂ : CategoryH _⇨₂_ _⇨₀_ ⦄
 where

open import Felix.Construct.Comma.Raw _⇨₀_ _⇨₁_ _⇨₂_

open import Felix.Boolean
open import Felix.Boolean.Homomorphism

module comma-booleans
    ⦃ _ : Products obj₁ ⦄  ⦃ _ : Products obj₂ ⦄  ⦃ _ : Products obj₀ ⦄
    ⦃ _ : Cartesian _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₀_ ⦄
    ⦃ _ : L.Cartesian _⇨₀_ ⦄
    ⦃ _ : ProductsH obj₁ _⇨₀_ ⦄  ⦃ _ : ProductsH obj₂ _⇨₀_ ⦄
    ⦃ _ : StrongProductsH obj₁ _⇨₀_ ⦄ ⦃ _ : StrongProductsH obj₂ _⇨₀_ ⦄
    ⦃ _ : CartesianH _⇨₁_ _⇨₀_ ⦄ ⦃ _ : CartesianH _⇨₂_ _⇨₀_ ⦄
    -- TODO: remove cartesian stuff as able
    ⦃ _ : Boolean obj₁ ⦄  ⦃ _ : Boolean obj₂ ⦄  ⦃ _ : Boolean obj₀ ⦄
    ⦃ _ : Logic _⇨₁_ ⦄ ⦃ _ : Logic _⇨₂_ ⦄ ⦃ _ : Logic _⇨₀_ ⦄
    -- ⦃ _ : L.Logic _⇨₀_ ⦄
    ⦃ _ : BooleanH obj₁ _⇨₀_ ⦄  ⦃ _ : BooleanH obj₂ _⇨₀_ ⦄
    ⦃ _ : StrongBooleanH obj₁ _⇨₀_ ⦄  ⦃ _ : StrongBooleanH obj₂ _⇨₀_ ⦄
    ⦃ _ : LogicH _⇨₁_ _⇨₀_ ⦄ ⦃ _ : LogicH _⇨₂_ _⇨₀_ ⦄
 where instance

  boolean : Boolean Obj
  boolean = record { 𝔹 = mkᵒ (β ∘ β⁻¹) } 

  -- The β and β⁻¹ here are from different BooleanHs.

  open Obj

  -- false′ : ⊤ ↬ 𝔹
  -- false′ = mkᵐ false false
  --   (begin
  --     h 𝔹 ∘ Fₘ false
  --    ≡⟨⟩
  --     (β ∘ β⁻¹) ∘ Fₘ false
  --    ≈⟨ ∘≈ʳ F-false′ ⟩
  --     (β ∘ β⁻¹) ∘ β ∘ false ∘ ε⁻¹
  --    ≈⟨ ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β) ⟩
  --     β ∘ false ∘ ε⁻¹
  --    -- (β ∘ false) ∘ ε⁻¹
  --    -- ((β ∘ false) ∘ ε⁻¹) ∘ (ε ∘ ε⁻¹)
  --    -- (β ∘ false ∘ ε⁻¹) ∘ (ε ∘ ε⁻¹)
  --    ≈˘⟨ (∘≈ˡ ∘-assocˡ ; cancelInner ε⁻¹∘ε ; ∘-assocʳ) ⟩
  --     (β ∘ false ∘ ε⁻¹) ∘ (ε ∘ ε⁻¹)
  --    ≈⟨ ∘≈ˡ (sym F-false′) ⟩
  --     Fₘ false ∘ (ε ∘ ε⁻¹)
  --    ≡⟨⟩
  --     Fₘ false ∘ h ⊤
  --    ∎)
  -- -- 45 sec

  false′ : ⊤ ↬ 𝔹
  false′ = mkᵐ false false
    ( ∘≈ʳ F-false′
    ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
    ; sym (∘≈ˡ (F-false′ ; ∘-assocˡ) ; cancelInner ε⁻¹∘ε ; ∘-assocʳ)
    )

  true′ : ⊤ ↬ 𝔹
  true′ = mkᵐ true true
    ( ∘≈ʳ F-true′
    ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
    ; sym (∘≈ˡ (F-true′ ; ∘-assocˡ) ; cancelInner ε⁻¹∘ε ; ∘-assocʳ)
    )

  -- not′ = mkᵐ not not
  --   (begin
  --      h 𝔹 ∘ Fₘ not
  --    ≡⟨⟩
  --      (β ∘ β⁻¹) ∘ Fₘ not
  --    ≈⟨ ∘≈ʳ F-not′ ⟩
  --      (β ∘ β⁻¹) ∘ (β ∘ not ∘ β⁻¹)
  --    ≈⟨ cancelInner β⁻¹∘β ⟩
  --      β ∘ not ∘ β⁻¹
  --    ≈⟨ sym (∘-assocˡʳ′ F-not) ⟩
  --      Fₘ not ∘ (β ∘ β⁻¹)
  --    ∎)

  not′ : 𝔹 ↬ 𝔹
  not′ = mkᵐ not not
    ( ∘≈ʳ F-not′
    ; cancelInner β⁻¹∘β
    ; sym (∘-assocˡʳ′ F-not)
    )

  -- nand′ : 𝔹 × 𝔹 ↬ 𝔹
  -- nand′ = mkᵐ nand nand
  --   (begin
  --      h 𝔹 ∘ Fₘ nand
  --    ≡⟨⟩
  --      (β ∘ β⁻¹) ∘ Fₘ nand
  --    ≈⟨ ∘≈ʳ F-nand′ ⟩
  --      (β ∘ β⁻¹) ∘ β ∘ nand ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
  --    ≈⟨ ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β) ⟩
  --      β ∘ nand ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
  --    ≈⟨ ∘-assocˡ′ (sym F-nand) ⟩
  --      (Fₘ nand ∘ μ ∘ (β ⊗ β)) ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
  --    ≈⟨ ∘-assocʳ′ ∘-assocʳ ⟩
  --      Fₘ nand ∘ μ ∘ (β ⊗ β) ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
  --    ≈⟨ ∘≈ʳ² (∘-assocˡ′ ⊗∘⊗) ⟩
  --      Fₘ nand ∘ μ ∘ ((β ∘ β⁻¹) ⊗ (β ∘ β⁻¹)) ∘ μ⁻¹
  --    ≡⟨⟩
  --      Fₘ nand ∘ μ ∘ (h 𝔹 ⊗ h 𝔹) ∘ μ⁻¹
  --    ≡⟨⟩
  --      Fₘ nand ∘ h (𝔹 × 𝔹)
  --    ∎)

  nand′ : 𝔹 × 𝔹 ↬ 𝔹
  nand′ = mkᵐ nand nand
          ( ∘≈ʳ F-nand′
          ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
          ; ∘-assocˡ′ (sym F-nand)
          ; ∘-assocʳ′ ∘-assocʳ
          ; ∘≈ʳ² (∘-assocˡ′ ⊗∘⊗)
          )

  nor′ : 𝔹 × 𝔹 ↬ 𝔹
  nor′ = mkᵐ nor nor
          ( ∘≈ʳ F-nor′
          ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
          ; ∘-assocˡ′ (sym F-nor)
          ; ∘-assocʳ′ ∘-assocʳ
          ; ∘≈ʳ² (∘-assocˡ′ ⊗∘⊗)
          )

  xor′ : 𝔹 × 𝔹 ↬ 𝔹
  xor′ = mkᵐ xor xor
            ( ∘≈ʳ F-xor′
            ; ∘-assocˡ′ (∘-assoc-elimʳ β⁻¹∘β)
            ; ∘-assocˡ′ (sym F-xor)
            ; ∘-assocʳ′ ∘-assocʳ
            ; ∘≈ʳ² (∘-assocˡ′ ⊗∘⊗)
            )

  instance

    logic : Logic _↬_
    logic = record { false = false′
                   ; true  = true′
                   ; not   = not′
                   ; nand  = nand′
                   ; nor   = nor′
                   ; xor   = xor′ }
