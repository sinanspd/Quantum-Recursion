module QuantumRec where
    open import Agda.Primitive using (Level; lzero)
    open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤?_ ; _≟_)
    open import Data.Bool using (Bool; true; false; if_then_else_)
    open import Data.Maybe using (Maybe; just; nothing)
    open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
    open import Data.List using (List; []; _∷_)
    open import Data.Fin using (Fin)
    open import Data.Vec using (Vec; []; _∷_; map; zipWith; lookup; updateAt)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
    open import Relation.Nullary.Decidable using (⌊_⌋)

    module Semantics (kC kQ : ℕ) where
        CVar : Set
        CVar = Fin kC

        QVar : Set
        QVar = Fin kQ

        ProcId : Set
        ProcId = ℕ

        UConst : Set
        UConst = ℕ

        postulate 
            Coeff : Set

        -- Classical Stuff 

        Store : Set 
        Store = Vec ℕ kC  

        get : Store → CVar → ℕ
        get s x = lookup s x

        set : Store → CVar → ℕ → Store
        set s x v = updateAt s x (λ _ → v) 

        getMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n
        getMany s []       = []
        getMany s (x ∷ xs) = get s x ∷ getMany s xs

        setMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n → Store
        setMany s []       []       = s
        setMany s (x ∷ xs) (v ∷ vs) = setMany (set s x v) xs vs

        -- do the expressions and evals for the expressions next 

        data Exp : Set where
            const : ℕ → Exp
            var   : CVar → Exp
            _+e_  : Exp → Exp → Exp
            _-e_  : Exp → Exp → Exp

        evalExp : Store → Exp → ℕ
        evalExp s (const n) = n 
        evalExp s (var x) = get s x 
        evalExp s (e₁ +e e₂) = evalExp s e₁ + evalExp s e₂
        evalExp σ (e₁ -e e₂) = evalExp σ e₁ ∸ evalExp σ e₂

        evalMany : ∀ {n} → Store → Vec Exp n → Vec ℕ n
        evalMany σ []       = []
        evalMany σ (e ∷ es) = evalExp σ e ∷ evalMany σ es

        -- yeah yeah I know cumbersome but better to have to pass these around as program expressions 
        data BExp : Set where 
            tt ff : BExp
            _≤e_  : Exp → Exp → BExp
            _≟e_  : Exp → Exp → BExp
            not   : BExp → BExp
            _and_ : BExp → BExp → BExp
            _or_  : BExp → BExp → BExp

        evalB : Store → BExp → Bool
        evalB s tt = true
        evalB s ff = false
        evalB s (e₁ ≤e e₂) = ⌊ evalExp s e₁ ≤? evalExp s e₂ ⌋
        evalB s (e₁ ≟e e₂) =  ⌊ evalExp s e₁ ≟ evalExp s e₂ ⌋
        evalB s (not b) = if evalB s b then false else true
        evalB s (b₁ and b₂) = if evalB s b₁ then evalB s b₂ else false
        evalB s (b₁ or  b₂) = if evalB s b₁ then true else evalB s b₂



         