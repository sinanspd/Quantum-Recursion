module QuantumRec where
    open import Agda.Primitive using (Level; lzero)
    open import Data.Nat using (ℕ; zero; suc; _+_; _-_; _≤?_ ; _≟_)
    open import Data.Bool using (Bool; true; false; if_then_else_)
    open import Data.Maybe using (Maybe; just; nothing)
    open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
    open import Data.List using (List; []; _∷_)
    open import Data.Fin using (Fin)
    open import Data.Vec using (Vec; []; _∷_; map; zipWith; lookup; updateAt)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

    module Semantics (κC κQ : ℕ) where
        CVar : Set
        CVar = Fin κC

        QVar : Set
        QVar = Fin κQ

        ProcId : Set
        ProcId = ℕ

        UConst : Set
        UConst = ℕ

        postulate: 
            Coeff: Set

        -- Classical Stuff 

        Store: Set 
        Store = Vec ℕ κC  

        get : Store → CVar → ℕ
        get σ x = lookup x σ

        set : Store → CVar → ℕ → Store
        set σ x v = updateAt x (λ _ → v) σ

        getMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n
        getMany σ []       = []
        getMany σ (x ∷ xs) = get σ x ∷ getMany σ xs

        setMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n → Store
        setMany σ []       []       = σ
        setMany σ (x ∷ xs) (v ∷ vs) = setMany (set σ x v) xs vs

        -- do the expressions and evals for the expressions next 
