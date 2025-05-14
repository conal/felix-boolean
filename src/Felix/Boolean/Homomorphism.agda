{-# OPTIONS --safe --without-K #-}

module Felix.Boolean.Homomorphism where

open import Level

open import Felix.Equiv
open import Felix.Raw
open import Felix.Laws as L hiding (Category; Cartesian; CartesianClosed)
open import Felix.Homomorphism
open import Felix.Reasoning

open import Felix.Boolean

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    obj₁ obj₂ : Set o
    a b c d : obj₁

record BooleanH
    (obj₁ : Set o₁) ⦃ _ : Boolean obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Boolean obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β   : 𝔹 ⇨₂ Fₒ 𝔹
    β⁻¹ : Fₒ 𝔹 ⇨₂ 𝔹

open BooleanH ⦃ … ⦄ public

id-BooleanH : {obj₂ : Set o} ⦃ _ : Boolean obj₂ ⦄
              {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
              ⦃ _ : Category _⇨₂_ ⦄
            → BooleanH obj₂ _⇨₂_ ⦃ Hₒ = id-Hₒ ⦄
id-BooleanH = record { β = id ; β⁻¹ = id }

record StrongBooleanH
    (obj₁ : Set o₁) ⦃ _ : Boolean obj₁ ⦄
    {obj₂ : Set o₂} ⦃ _ : Boolean obj₂ ⦄ (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    {q : Level} ⦃ _ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Category _⇨₂′_ ⦄
    ⦃ booleanH : BooleanH obj₁ _⇨₂′_  ⦄
    : Set (o₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β⁻¹∘β : β⁻¹ ∘ β ≈ id
    β∘β⁻¹ : β ∘ β⁻¹ ≈ id

open StrongBooleanH ⦃ … ⦄ public

id-StrongBooleanH : 
      {obj₂ : Set o}  ⦃ _ : Boolean obj₂ ⦄
      {_⇨₂_ : obj₂ → obj₂ → Set ℓ₂}
      ⦃ _ : Category _⇨₂_ ⦄
      {q : Level} ⦃ _ : Equivalent q _⇨₂_ ⦄
      ⦃ _ : BooleanH obj₂ _⇨₂_ ⦃ Hₒ = id-Hₒ ⦄ ⦄
      ⦃ _ : L.Category _⇨₂_ ⦄
  → StrongBooleanH obj₂ _⇨₂_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ booleanH = id-BooleanH ⦄
id-StrongBooleanH = record
    { β⁻¹∘β = identityˡ
    ; β∘β⁻¹ = identityˡ
    }

record LogicH
    {obj₁ : Set o₁} (_⇨₁′_ : obj₁ → obj₁ → Set ℓ₁)
    {obj₂ : Set o₂} (_⇨₂′_ : obj₂ → obj₂ → Set ℓ₂)
    {q} ⦃ eq₂ : Equivalent q _⇨₂′_ ⦄
    ⦃ _ : Boolean obj₁ ⦄ ⦃ _ : Products obj₁ ⦄ ⦃ _ : Logic _⇨₁′_ ⦄
    ⦃ _ : Boolean obj₂ ⦄ ⦃ _ : Products obj₂ ⦄ ⦃ _ : Logic _⇨₂′_ ⦄
    ⦃ _ : Category _⇨₂′_ ⦄ ⦃ _ : Cartesian _⇨₂′_ ⦄
    ⦃ Hₒ : Homomorphismₒ obj₁ obj₂ ⦄
    ⦃ H : Homomorphism _⇨₁′_ _⇨₂′_ ⦄
    ⦃ pH : ProductsH obj₁ _⇨₂′_ ⦄
    ⦃ spH : StrongProductsH obj₁ _⇨₂′_ ⦄
    ⦃ booleanH  : BooleanH obj₁ _⇨₂′_ ⦄
  : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₁_; _⇨₁_ = _⇨₁′_
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  open ≈-Reasoning ⦃ eq₂ ⦄

  field
    F-false : Fₘ false ∘ ε ≈ β ∘ false
    F-true  : Fₘ true  ∘ ε ≈ β ∘ true
    F-not   : Fₘ not ∘ β ≈ β ∘ not
    F-nand  : Fₘ nand ∘ μ ∘ (β ⊗ β) ≈ β ∘ nand
    F-nor   : Fₘ nor  ∘ μ ∘ (β ⊗ β) ≈ β ∘ nor
    F-xor   : Fₘ xor  ∘ μ ∘ (β ⊗ β) ≈ β ∘ xor

  module _ ⦃ _ : L.Category _⇨₂_ ⦄ ⦃ _ : L.Cartesian _⇨₂_ ⦄
           ⦃ _ : StrongBooleanH obj₁ _⇨₂_ ⦄ where

    F-false′ : Fₘ false ≈ β ∘ false ∘ ε⁻¹
    F-false′ = sym≈ (∘-assoc-elimʳ ε∘ε⁻¹) ; ∘≈ˡ F-false ; ∘-assocʳ

    -- F-false′ =
    --   begin
    --     Fₘ false
    --   ≈⟨ sym (∘-assoc-elimʳ ε∘ε⁻¹) ⟩
    --     (Fₘ false ∘ ε) ∘ ε⁻¹
    --   ≈⟨ ∘≈ˡ F-false ⟩
    --     (β ∘ false) ∘ ε⁻¹
    --   ≈⟨ ∘-assocʳ ⟩
    --     β ∘ false ∘ ε⁻¹
    --   ∎

    F-true′ : Fₘ true ≈ β ∘ true ∘ ε⁻¹
    F-true′ = sym≈ (∘-assoc-elimʳ ε∘ε⁻¹) ; ∘≈ˡ F-true ; ∘-assocʳ

    F-not′ : Fₘ not ≈ β ∘ not ∘ β⁻¹
    F-not′ = sym≈ (∘-assoc-elimʳ β∘β⁻¹) ; ∘≈ˡ F-not ; ∘-assocʳ

    -- F-not′ =
    --   begin
    --     Fₘ not
    --   ≈⟨ sym (∘-assoc-elimʳ β∘β⁻¹) ⟩
    --     (Fₘ not ∘ β) ∘ β⁻¹
    --   ≈⟨ ∘≈ˡ F-not ⟩
    --     (β ∘ not) ∘ β⁻¹
    --   ≈⟨ ∘-assocʳ ⟩
    --     β ∘ not ∘ β⁻¹
    --   ∎

    F-nand′ : Fₘ nand ≈ β ∘ nand ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    F-nand′ = sym≈ (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ β∘β⁻¹)))
            ; ∘≈ˡ F-nand ; ∘-assocʳ

    -- F-nand′ : Fₘ nand ≈ β ∘ nand ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    -- F-nand′ =
    --   begin
    --     Fₘ nand
    --   ≈⟨ sym (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ β∘β⁻¹))) ⟩
    --     (Fₘ nand ∘ μ ∘ (β ⊗ β)) ∘ ((β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹)
    --   ≈⟨ ∘≈ˡ F-nand ⟩
    --     (β ∘ nand) ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    --   ≈⟨ ∘-assocʳ ⟩
    --     β ∘ nand ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    --   ∎

    F-nor′ : Fₘ nor ≈ β ∘ nor ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    F-nor′ = sym≈ (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ β∘β⁻¹)))
           ; ∘≈ˡ F-nor ; ∘-assocʳ

    F-xor′ : Fₘ xor ≈ β ∘ xor ∘ (β⁻¹ ⊗ β⁻¹) ∘ μ⁻¹
    F-xor′ = sym≈ (∘-assoc-elimʳ (∘-inverse μ∘μ⁻¹ (⊗-inverse β∘β⁻¹ β∘β⁻¹)))
           ; ∘≈ˡ F-xor ; ∘-assocʳ

open LogicH ⦃ … ⦄ public

id-LogicH : {obj : Set o} ⦃ _ : Products obj ⦄ ⦃ _ : Boolean obj ⦄
            {_⇨_ : obj → obj → Set ℓ}
            {q : Level} ⦃ eq : Equivalent q _⇨_ ⦄
            ⦃ _ :   Category _⇨_ ⦄ ⦃ _ :   Cartesian _⇨_ ⦄ ⦃ _ :   Logic _⇨_ ⦄
            ⦃ _ : L.Category _⇨_ ⦄ ⦃ _ : L.Cartesian _⇨_ ⦄ -- ⦃ _ : L.Logic _⇨_ ⦄
          → LogicH _⇨_ _⇨_ ⦃ Hₒ = id-Hₒ ⦄ ⦃ H = id-H ⦄
               ⦃ pH = id-ProductsH ⦄ ⦃ spH = id-StrongProductsH ⦄
               ⦃ booleanH = id-BooleanH ⦄
id-LogicH ⦃ eq = eq ⦄ = record
                          { F-false = identityʳ ; sym≈ identityˡ
                          ; F-true  = identityʳ ; sym≈ identityˡ
                          ; F-not   = identityʳ ; sym≈ identityˡ
                          ; F-nand  = elimʳ (identityˡ ; id⊗id) ; sym≈ identityˡ
                          ; F-nor   = elimʳ (identityˡ ; id⊗id) ; sym≈ identityˡ
                          ; F-xor   = elimʳ (identityˡ ; id⊗id) ; sym≈ identityˡ
                          }
 where open ≈-Reasoning ⦃ eq ⦄
