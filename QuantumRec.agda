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

    module Semantics (kC kQ : ℕ) where
        CVar : Set
        CVar = Fin kC

        QVar : Set
        QVar = Fin kQ

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
        get s x = lookup x s

        set : Store → CVar → ℕ → Store
        set s x v = updateAt x (λ _ → v) s

        getMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n
        getMany s []       = []
        getMany s (x ∷ xs) = get s x ∷ getMany s xs

        setMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n → Store
        setMany s []       []       = s
        setMany s (x ∷ xs) (v ∷ vs) = setMany (set s x v) xs vs

        -- do the expressions and evals for the expressions next 
