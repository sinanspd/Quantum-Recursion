module QuantumRec where

open import Agda.Primitive using (Level; lzero)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≟_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Vec using (Vec; []; _∷_; map; lookup; updateAt)
open import Data.Fin using (Fin; _≟_)  
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.List as List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

module Semantics (kC kQ : ℕ) where


  ---------------- 
  -- Basic definitions
  ----------------  

  CVar : Set
  CVar = Fin kC

  QVar : Set
  QVar = Fin kQ

  ProcId : Set
  ProcId = ℕ

  UConst : Set
  UConst = ℕ

  Coeff : Set
  Coeff = ℕ

  Store : Set
  Store = Vec ℕ kC

  get : Store → CVar → ℕ
  get σ x = lookup σ x

  set : Store → CVar → ℕ → Store
  set σ x v = updateAt σ x (λ _ → v)

  getMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n
  getMany σ []       = []
  getMany σ (x ∷ xs) = get σ x ∷ getMany σ xs

  setMany : ∀ {n} → Store → Vec CVar n → Vec ℕ n → Store
  setMany σ []       []       = σ
  setMany σ (x ∷ xs) (v ∷ vs) = setMany (set σ x v) xs vs

  data Exp : Set where
    const : ℕ → Exp
    var   : CVar → Exp
    _+e_  : Exp → Exp → Exp
    _-e_  : Exp → Exp → Exp

  evalExp : Store → Exp → ℕ
  evalExp σ (const n)  = n
  evalExp σ (var x)    = get σ x
  evalExp σ (e₁ +e e₂) = evalExp σ e₁ + evalExp σ e₂
  evalExp σ (e₁ -e e₂) = evalExp σ e₁ ∸ evalExp σ e₂

  evalMany : ∀ {n} → Store → Vec Exp n → Vec ℕ n
  evalMany σ []       = []
  evalMany σ (e ∷ es) = evalExp σ e ∷ evalMany σ es

  data QState : Set where
    atom  : ℕ → QState
    aply  : UConst → QState → QState
    split : ∀ {m d} → Vec QVar m → Vec Coeff d → Vec QState d → QState

  data Cmd : Set where
    skip  : Cmd
    halt  : Cmd

    assign : ∀ {n} → Vec CVar n → Vec Exp n → Cmd
    gate   : ∀ {n} → UConst → Vec QVar n → Cmd
    seq    : Cmd → Cmd → Cmd

    qif    : ∀ {m d} → Vec QVar m → Vec Cmd d → Cmd

    beginLocal : ∀ {n} → Vec CVar n → Vec Exp n → Cmd → Cmd

    call0  : ProcId → Cmd
    callN  : ∀ {n} → ProcId → Vec Exp n → Cmd

  data DeclItem : Set where
    decl0 : ProcId → Cmd → DeclItem
    declN : ∀ {n} → ProcId → Vec CVar n → Cmd → DeclItem

  Decls : Set
  Decls = List DeclItem

  data HasDecl0 : ProcId → Cmd → Decls → Set where
    here0  : ∀ {P C ds} → HasDecl0 P C (decl0 P C ∷ᴸ ds)
    there0 : ∀ {P C d ds} → HasDecl0 P C ds → HasDecl0 P C (d ∷ᴸ ds)

  data HasDeclN : ∀ {n} → ProcId → Vec CVar n → Cmd → Decls → Set where
    hereN  : ∀ {n P xs C ds} → HasDeclN {n} P xs C (declN {n} P xs C ∷ᴸ ds)
    thereN : ∀ {n P xs C d ds} → HasDeclN {n} P xs C ds → HasDeclN {n} P xs C (d ∷ᴸ ds)

  find0 : (P : ProcId) → (D : Decls) → Maybe (Σ Cmd (λ C → HasDecl0 P C D))
  find0 P []ᴸ = nothing
  find0 P (decl0 P' C ∷ᴸ ds) with P Data.Nat.≟ P'
  ... | yes refl = just (C , here0)
  ... | no  _ with find0 P ds
  ...   | nothing = nothing
  ...   | just (C' , h) = just (C' , there0 h)
  find0 P (declN P' xs C ∷ᴸ ds) with find0 P ds
  ... | nothing = nothing
  ... | just (C' , h) = just (C' , there0 h)

  findN : ∀ {n} → (P : ProcId) → (D : Decls)
        → Maybe (Σ (Vec CVar n) (λ xs → Σ Cmd (λ C → HasDeclN {n} P xs C D)))
  findN {n} P []ᴸ = nothing
  findN {n} P (decl0 P' C ∷ᴸ ds) with findN {n} P ds
  ... | nothing = nothing
  ... | just (xs , (C' , h)) = just (xs , (C' , thereN h))
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) with P Data.Nat.≟ P'
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | no _ with findN {n} P ds
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | no _ | nothing = nothing
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | no _ | just (xs' , (C' , h)) = just (xs' , (C' , thereN h))
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl with n Data.Nat.≟ n'
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl | no _ with findN {n} P ds
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl | no _ | nothing = nothing
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl | no _ | just (xs' , (C' , h)) = just (xs' , (C' , thereN h))
  findN {n} P (declN {n'} P' xs C ∷ᴸ ds) | yes refl | yes refl = just (xs , (C , hereN))

  record Config : Set where
    constructor ⟨_,_,_⟩
    field
      cmd : Cmd
      st  : Store
      qs  : QState
  open Config public


  -----------------
  --- Rules from the paper
  ----------------

  mutual
    data Step (D : Decls) : Config → Config → Set where
      SK : ∀ {σ ψ}
         → Step D ⟨ skip , σ , ψ ⟩ ⟨ halt , σ , ψ ⟩

      AS : ∀ {n} {xs : Vec CVar n} {ts : Vec Exp n} {σ ψ}
         → Step D ⟨ assign xs ts , σ , ψ ⟩
                  ⟨ halt , setMany σ xs (evalMany σ ts) , ψ ⟩

      GA : ∀ {n} {U : UConst} {qs : Vec QVar n} {σ ψ}
         → Step D ⟨ gate U qs , σ , ψ ⟩
                  ⟨ halt , σ , aply U ψ ⟩

      SC : ∀ {C₁ C₁' C₂ σ σ' ψ ψ'}
         → Step D ⟨ C₁ , σ , ψ ⟩ ⟨ C₁' , σ' , ψ' ⟩
         → Step D ⟨ seq C₁ C₂ , σ , ψ ⟩ ⟨ seq C₁' C₂ , σ' , ψ' ⟩

      SC-halt : ∀ {C₂ σ ψ}
              → Step D ⟨ seq halt C₂ , σ , ψ ⟩ ⟨ C₂ , σ , ψ ⟩

      BS : ∀ {n} {xs : Vec CVar n} {ts : Vec Exp n} {C σ ψ}
         → Step D ⟨ beginLocal xs ts C , σ , ψ ⟩
                  ⟨ seq (assign xs ts)
                        (seq C (assign xs (map const (getMany σ xs))))
                  , σ , ψ ⟩

      CR : ∀ {P C σ ψ}
         → HasDecl0 P C D
         → Step D ⟨ call0 P , σ , ψ ⟩ ⟨ C , σ , ψ ⟩

      RC : ∀ {n} {P : ProcId} {args : Vec Exp n} {xs : Vec CVar n} {C σ ψ}
         → HasDeclN {n} P xs C D
         → Step D ⟨ callN P args , σ , ψ ⟩
                  ⟨ beginLocal xs args C , σ , ψ ⟩

      QC : ∀ {m d}
           {coin : Vec QVar m}
           {branches : Vec Cmd d}
           {α : Vec Coeff d}
           {θ θ' : Vec QState d}
           {σ σ' : Store}
         → BranchSteps D branches σ θ σ' θ'
         → Step D ⟨ qif coin branches , σ , split coin α θ ⟩
                  ⟨ halt , σ' , split coin α θ' ⟩

    data Steps (D : Decls) : Config → Config → Set where
      refl  : ∀ {x} → Steps D x x
      trans : ∀ {x y z} → Step D x y → Steps D y z → Steps D x z

    data BranchSteps (D : Decls) :
      ∀ {d} → Vec Cmd d → Store → Vec QState d → Store → Vec QState d → Set where
      bs-nil  : ∀ {σ σ'} → BranchSteps D [] σ [] σ' []
      bs-cons : ∀ {d C Cs σ σ' θ θs θ' θs'}
              → Steps D ⟨ C , σ , θ ⟩ ⟨ halt , σ' , θ' ⟩
              → BranchSteps D Cs σ θs σ' θs'
              → BranchSteps D (C ∷ Cs) σ (θ ∷ θs) σ' (θ' ∷ θs')

  steps-single : ∀ {D x y} → Step D x y → Steps D x y
  steps-single s = Steps.trans s Steps.refl

  steps-++ : ∀ {D x y z} → Steps D x y → Steps D y z → Steps D x z
  steps-++ Steps.refl          s₂ = s₂
  steps-++ (Steps.trans s s₁)  s₂ = Steps.trans s (steps-++ s₁ s₂)

  liftSeq : ∀ {D C₁ C₂ σ ψ C₁' σ' ψ'}
          → Steps D ⟨ C₁  , σ  , ψ  ⟩ ⟨ C₁' , σ' , ψ' ⟩
          → Steps D ⟨ seq C₁ C₂ , σ  , ψ  ⟩ ⟨ seq C₁' C₂ , σ' , ψ' ⟩
  liftSeq Steps.refl = Steps.refl
  liftSeq (Steps.trans s ss) = Steps.trans (SC s) (liftSeq ss)

  storeEq : Store → Store → Bool
  storeEq = vecEq
    where
      vecEq : ∀ {n} → Vec ℕ n → Vec ℕ n → Bool
      vecEq []       []       = true
      vecEq (x ∷ xs) (y ∷ ys) with ⌊ x Data.Nat.≟ y ⌋
      ... | true  = vecEq xs ys
      ... | false = false

  coinEq : ∀ {m} → Vec QVar m → Vec QVar m → Bool
  coinEq []       []       = true
  coinEq (x ∷ xs) (y ∷ ys) with ⌊ x Data.Fin.≟ y ⌋
  ... | true  = coinEq xs ys
  ... | false = false

  coinEqAny : ∀ {m n} → Vec QVar m → Vec QVar n → Bool
  coinEqAny {m} {n} xs ys with m Data.Nat.≟ n
  ... | no _ = false
  ... | yes refl = coinEq xs ys

  ---------------- 
  -- Eval Rules 
  ----------------

  mutual
    eval : ℕ → Decls → Cmd → Store → QState → Maybe (Store × QState)
    eval zero    D C σ ψ = nothing
    eval (suc k) D skip σ ψ = just (σ , ψ)
    eval (suc k) D halt σ ψ = just (σ , ψ)

    eval (suc k) D (assign xs ts) σ ψ =
      just (setMany σ xs (evalMany σ ts) , ψ)

    eval (suc k) D (gate U qs) σ ψ =
      just (σ , aply U ψ)

    eval (suc k) D (seq C₁ C₂) σ ψ with eval k D C₁ σ ψ
    ... | nothing        = nothing
    ... | just (σ₁ , ψ₁) = eval k D C₂ σ₁ ψ₁

    eval (suc k) D (beginLocal xs ts C) σ ψ =
      eval k D (seq (assign xs ts)
                  (seq C (assign xs (map const (getMany σ xs)))))
           σ ψ

    eval (suc k) D (call0 P) σ ψ with find0 P D
    ... | nothing        = nothing
    ... | just (C , h)   = eval k D C σ ψ

    eval (suc k) D (callN {n} P args) σ ψ with findN {n} P D
    ... | nothing                  = nothing
    ... | just (xs , (C , h))      = eval k D (beginLocal xs args C) σ ψ

    eval (suc k) D (qif {m} {d} coin branches) σ ψ = evalQif k D coin branches σ ψ

    evalQif : ∀ {m d} → ℕ → Decls → Vec QVar m → Vec Cmd d → Store → QState → Maybe (Store × QState)
    evalQif {m} {d} k D coin branches σ (split {m = m'} {d = d'} coin' α θ) 
      with coinEqAny coin coin' | d Data.Nat.≟ d'
    ... | false | _ = nothing
    ... | _ | no _ = nothing
    ... | true | yes refl with evalBranches k D branches σ θ
    ...   | nothing = nothing
    ...   | just (σ' , θ') = just (σ' , split coin α θ')
    evalQif k D coin branches σ ψ = nothing

    evalBranches :
      ∀ {d} → ℕ → Decls → Vec Cmd d → Store → Vec QState d
            → Maybe (Store × Vec QState d)
    evalBranches fuel D [] σ [] = just (σ , [])
    evalBranches fuel D (C ∷ Cs) σ (θ ∷ θs) with eval fuel D C σ θ
    ... | nothing = nothing
    ... | just (σ₁ , θ₁) with evalBranches fuel D Cs σ θs
    ...   | nothing = nothing
    ...   | just (σ₂ , θs') =
          if storeEq σ₁ σ₂ then just (σ₁ , θ₁ ∷ θs') else nothing

