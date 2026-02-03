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


        -- Now the fun stuff 

        data QState : Set where 
            atom : ℕ → QState
            aply   : UConst → QState → QState
            split : ∀ {m d} → Vec QVar m → Vec Coeff d → Vec QState d → QState -- this term comes from the paper 

        data Cmd : Set where 
            skip : Cmd 
            halt : Cmd -- ↓ terminal marker, need otherwise termination not proveable 
            assign : ∀ {n} → Vec CVar n → Vec Exp n → Cmd
            gate   : ∀ {n} → UConst → Vec QVar n → Cmd
            seq    : Cmd → Cmd → Cmd
            if_    : BExp → Cmd → Cmd → Cmd
            while_ : BExp → Cmd → Cmd
            qif    : ∀ {m d} → Vec QVar m → Vec Cmd d → Cmd
            beginLocal : ∀ {n} → Vec CVar n → Vec Exp n → Cmd → Cmd
            call0  : ProcId → Cmd
            callN  : ProcId → (Σ ℕ (λ n → Vec Exp n)) → Cmd

        
        record DeclN : Set where
            constructor mkDeclN
            field
                pid     : ProcId
                arity   : ℕ
                formals : Vec CVar arity
                body    : Cmd

        data DeclItem : Set where
            decl0 : ProcId → Cmd → DeclItem
            declN : DeclN → DeclItem

        Decls : Set
        Decls = List DeclItem

        lookup0 : ProcId → Decls → Maybe Cmd
        lookup0 P [] = nothing
        lookup0 P (decl0 P' C ∷ ds) with ⌊ P ≟ P' ⌋
        ... | true  = just C
        ... | false = lookup0 P ds
        lookup0 P (_ ∷ ds) = lookup0 P ds

        lookupN : ProcId → Decls → Maybe DeclN
        lookupN P [] = nothing
        lookupN P (declN d ∷ ds) with ⌊ P ≟ DeclN.pid d ⌋
        ... | true  = just d
        ... | false = lookupN P ds
        lookupN P (_ ∷ ds) = lookupN P ds

        record Config : Set where
            constructor ⟨_,_,_⟩
            field 
                c : Cmd
                σ : Store
                ψ : QState
        open Config public

        data C3 {A B C : Set} (P : A → B → C → Set) :
                    ∀ {n} → Vec A n → Vec B n → Vec C n → Set where
            c3nil  : C3 P [] [] []
            c3cons : ∀ {n a b c as bs cs}
                    → P a b c
                    → C3 P as bs cs
                    → C3 P (a ∷ as) (b ∷ bs) (c ∷ cs)

        mutual 
            data Step (D : Decls) : Config → Config → Set where
                SK : ∀ {σ ψ} → Step D ⟨ skip , σ , ψ ⟩ ⟨ halt , σ , ψ ⟩

                -- rest of the rules in the paper TBD 


        data Steps (D : Decls) : Config → Config → Set where
            refl  : ∀ {x} → Steps D x x
            trans : ∀ {x y z} → Step D x y → Steps D y z → Steps D x z