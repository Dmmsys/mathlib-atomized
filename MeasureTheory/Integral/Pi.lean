/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integration with respect to a finite product of measures

On a finite product of measure spaces, we show that a product of integrable functions each
depending on a single coordinate is integrable, in `MeasureTheory.integrable_fintype_prod`, and
that its integral is the product of the individual integrals,
in `MeasureTheory.integral_fintype_prod_eq_prod`.
-/

public section

open Fintype MeasureTheory MeasureTheory.Measure

namespace MeasureTheory

variable {𝕜 ι : Type*} [Fintype ι]

namespace Integrable

variable [NormedCommRing 𝕜]

/-- On a finite product space in `n` variables, for a natural number `n`, a product of integrable
functions depending on each coordinate is integrable. -/
/-
**MeasureTheory.Integrable.fin_nat_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：fin_nat_prod {n : Nat} {E : Fin n -> Type*} {mE : forall i, MeasurableSpac
e (E i)} {μ : (i : Fin n) -> Measure (E i)} [forall i, SigmaFinite (μ i)] {f : (
i : Fin n) -> E i -> 𝕜} (hf : forall i, Integrable (f i) (μ i)) : Integrable (fu
n (x : (i : Fin n) -> E i) => ∏ i, f i (x i)) (Measure.pi μ)
参数：E i；i : Fin n；E i；μ i；i : Fin n；hf : forall i, Integrable (f i) (μ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `MeasureTheory.Measure.pi_empty_univ`：pi_empty_univ {α : Type*} [Fintype 
α] [IsEmpty α] {β : α -> Type*} {m : forall α, MeasurableSpace (β α)} (μ : foral
l a : α, Measure (β a)) :…
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.measurePreserving_piFinSuccAbove`：measurePreserving_piFinS
uccAbove {n : Nat} {α : Fin (n + 1) -> Type u} {m : forall i, MeasurableSpace (α
 i)} (μ : forall i, Measure (α i)) […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp_emb`：∀ {α : Type u_1} {δ
 : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `MeasurableEquiv.piFinSuccAbove_symm_apply`：∀ {n : ℕ} (α : Fin (n + 1) → 
Type u_8) [inst : (i : Fin (n + 1)) → MeasurableSpace (α i)] (i : Fin (n + 1)), 
  ⇑(MeasurableEquiv.piFinSuccAb…
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Fin.succAbove_zero`：∀ {n : ℕ}, Fin.succAbove 0 = Fin.succ
· 使用定理 `Fin.insertNth_zero`：insertNth_zero (x : α 0) (p : forall j : Fin n, α (s
uccAbove 0 j)) : insertNth 0 x p = cons x fun j => _root_.cast (congr_arg α (con
gr_fun s…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `MeasureTheory.Integrable.mul_prod`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {ν : MeasureTheory.M…

--- 原说明 ---
On a finite product space in `n` variables, for a natural number `n`, a product 
of integrable
functions depending on each coordinate is integrable.
-/
theorem fin_nat_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → 𝕜} (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun (x : (i : Fin n) → E i) ↦ ∏ i, f i (x i)) (Measure.pi μ) := by
  induction n with
  | zero => simp only [Finset.univ_eq_empty, Finset.prod_empty, isFiniteMeasure_iff,
      integrable_const_iff, pi_empty_univ, ENNReal.one_lt_top, or_true]
  | succ n n_ih =>
      have := ((measurePreserving_piFinSuccAbove μ 0).symm)
      rw [← this.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero]
      simp only [Fin.zero_succAbove, Function.comp_def]
      have : Integrable (fun (x : (j : Fin n) → E (Fin.succ j)) ↦ ∏ j, f (Fin.succ j) (x j))
          (Measure.pi (fun i ↦ μ i.succ)) :=
        n_ih (fun i ↦ hf _)
      exact Integrable.mul_prod (hf 0) this

/-- On a finite product space, a product of integrable functions depending on each coordinate is
integrable. Version with dependent target. -/
/-
**MeasureTheory.Integrable.fintype_prod_dep** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Integrable`。
形式化陈述：fintype_prod_dep {E : ι -> Type*} {f : (i : ι) -> E i -> 𝕜} {mE : forall i
, MeasurableSpace (E i)} {μ : (i : ι) -> Measure (E i)} [forall i, SigmaFinite (
μ i)] (hf : forall i, Integrable (f i) (μ i)) : Integrable (fun (x : (i : ι) -> 
E i) => ∏ i, f i (x i)) (Measure.pi μ)
参数：i : ι；E i；i : ι；E i；μ i；hf : forall i, Integrable (f i) (μ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp_emb`：∀ {α : Type u_1} {δ
 : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `MeasureTheory.measurePreserving_piCongrLeft`：measurePreserving_piCongrLe
ft (f : ι' ≃ ι) : MeasurePreserving (MeasurableEquiv.piCongrLeft α f) (Measure.p
i fun i' => μ (f i')) (Measure.pi…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `MeasurableEquiv.coe_piCongrLeft`：coe_piCongrLeft (f : δ ≃ δ') : ⇑(Measur
ableEquiv.piCongrLeft π f) = f.piCongrLeft π
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Equiv.piCongrLeft_apply_apply`：piCongrLeft_apply_apply (f : forall a, P 
(e a)) (a : α) : (piCongrLeft P e) f (e a) = f a
· 使用定理 `MeasureTheory.Integrable.fin_nat_prod`：fin_nat_prod {n : Nat} {E : Fin n
 -> Type*} {mE : forall i, MeasurableSpace (E i)} {μ : (i : Fin n) -> Measure (E
 i)} [forall i, SigmaFinite…

--- 原说明 ---
On a finite product space, a product of integrable functions depending on each c
oordinate is
integrable. Version with dependent target.
-/
theorem fintype_prod_dep {E : ι → Type*}
    {f : (i : ι) → E i → 𝕜} {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun (x : (i : ι) → E i) ↦ ∏ i, f i (x i)) (Measure.pi μ) := by
  let e := (equivFin ι).symm
  simp_rw [← (measurePreserving_piCongrLeft _ e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _),
    ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Function.comp_def,
    Equiv.piCongrLeft_apply_apply]
  exact .fin_nat_prod (fun i ↦ hf _)

/-- On a finite product space, a product of integrable functions depending on each coordinate is
integrable. -/
/-
**MeasureTheory.Integrable.fintype_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Integrable`。
形式化陈述：fintype_prod {E : Type*} {f : ι -> E -> 𝕜} {mE : MeasurableSpace E} {μ : ι
 -> Measure E} [forall i, SigmaFinite (μ i)] (hf : forall i, Integrable (f i) (μ
 i)) : Integrable (fun (x : ι -> E) => ∏ i, f i (x i)) (Measure.pi μ)
参数：μ i；hf : forall i, Integrable (f i) (μ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.fintype_prod_dep`：fintype_prod_dep {E : ι -> Ty
pe*} {f : (i : ι) -> E i -> 𝕜} {mE : forall i, MeasurableSpace (E i)} {μ : (i : 
ι) -> Measure (E i)} [forall i,…

--- 原说明 ---
On a finite product space, a product of integrable functions depending on each c
oordinate is
integrable.
-/
theorem fintype_prod {E : Type*}
    {f : ι → E → 𝕜} {mE : MeasurableSpace E} {μ : ι → Measure E} [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Integrable (f i) (μ i)) :
    Integrable (fun (x : ι → E) ↦ ∏ i, f i (x i)) (Measure.pi μ) :=
  Integrable.fintype_prod_dep hf

end Integrable

variable [RCLike 𝕜]

set_option backward.isDefEq.respectTransparency false in
/-- A version of **Fubini's theorem** in `n` variables, for a natural number `n`. -/
/-
**MeasureTheory.integral_fin_nat_prod_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_fin_nat_prod_eq_prod {n : Nat} {E : Fin n -> Type*} {mE : forall 
i, MeasurableSpace (E i)} {μ : (i : Fin n) -> Measure (E i)} [forall i, SigmaFin
ite (μ i)] (f : (i : Fin n) -> E i -> 𝕜) : ∫ x : (i : Fin n) -> E i, ∏ i, f i (x
 i) ∂(Measure.pi μ) = ∏ i, ∫ x, f i x ∂(μ i)
参数：E i；i : Fin n；E i；μ i；f : (i : Fin n) -> E i -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.pi_empty_univ`：pi_empty_univ {α : Type*} [Fintype 
α] [IsEmpty α] {β : α -> Type*} {m : forall α, MeasurableSpace (β α)} (μ : foral
l a : α, Measure (β a)) :…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp'`：∀ {α : Type u_1} {G : Ty
pe u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : Measurable
Space α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.measurePreserving_piFinSuccAbove`：measurePreserving_piFinS
uccAbove {n : Nat} {α : Fin (n + 1) -> Type u} {m : forall i, MeasurableSpace (α
 i)} (μ : forall i, Measure (α i)) […
· 使用定理 `MeasurableEquiv.piFinSuccAbove_symm_apply`：∀ {n : ℕ} (α : Fin (n + 1) → 
Type u_8) [inst : (i : Fin (n + 1)) → MeasurableSpace (α i)] (i : Fin (n + 1)), 
  ⇑(MeasurableEquiv.piFinSuccAb…
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Fin.succAbove_zero`：∀ {n : ℕ}, Fin.succAbove 0 = Fin.succ
· 使用定理 `Fin.insertNth_zero`：insertNth_zero (x : α 0) (p : forall j : Fin n, α (s
uccAbove 0 j)) : insertNth 0 x p = cons x fun j => _root_.cast (congr_arg α (con
gr_fun s…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
A version of **Fubini's theorem** in `n` variables, for a natural number `n`.
-/
theorem integral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → 𝕜) :
    ∫ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp [measureReal_def]
  | succ n n_ih =>
      calc
        _ = ∫ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih, ← integral_prod_mul]
        _ = ∏ i, ∫ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- A version of **Fubini's theorem** in `n` variables, for a natural number `n`. -/
/-
**MeasureTheory.integral_fin_nat_prod_volume_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：integral_fin_nat_prod_volume_eq_prod {n : Nat} {E : Fin n -> Type*} [foral
l i, MeasureSpace (E i)] [forall i, SigmaFinite (volume : Measure (E i))] (f : (
i : Fin n) -> E i -> 𝕜) : ∫ x : (i : Fin n) -> E i, ∏ i, f i (x i) = ∏ i, ∫ x, f
 i x
参数：E i；volume : Measure (E i)；f : (i : Fin n) -> E i -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_fin_nat_prod_eq_prod`：integral_fin_nat_prod_eq_pr
od {n : Nat} {E : Fin n -> Type*} {mE : forall i, MeasurableSpace (E i)} {μ : (i
 : Fin n) -> Measure (E i)} [fora…

--- 原说明 ---
A version of **Fubini's theorem** in `n` variables, for a natural number `n`.
-/
theorem integral_fin_nat_prod_volume_eq_prod {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))]
    (f : (i : Fin n) → E i → 𝕜) :
    ∫ x : (i : Fin n) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := integral_fin_nat_prod_eq_prod _

/-- A version of **Fubini's theorem** with the variables indexed by a general finite type. -/
/-
**MeasureTheory.integral_fintype_prod_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_fintype_prod_eq_prod {E : ι -> Type*} (f : (i : ι) -> E i -> 𝕜) {
mE : forall i, MeasurableSpace (E i)} {μ : (i : ι) -> Measure (E i)} [forall i, 
SigmaFinite (μ i)] : ∫ x : (i : ι) -> E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i,
 ∫ x, f i x ∂(μ i)
参数：f : (i : ι) -> E i -> 𝕜；E i；i : ι；E i；μ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp'`：∀ {α : Type u_1} {G : Ty
pe u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : Measurable
Space α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.measurePreserving_piCongrLeft`：measurePreserving_piCongrLe
ft (f : ι' ≃ ι) : MeasurePreserving (MeasurableEquiv.piCongrLeft α f) (Measure.p
i fun i' => μ (f i')) (Measure.pi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasurableEquiv.coe_piCongrLeft`：coe_piCongrLeft (f : δ ≃ δ') : ⇑(Measur
ableEquiv.piCongrLeft π f) = f.piCongrLeft π
· 使用引理 `Equiv.piCongrLeft_apply_apply`：piCongrLeft_apply_apply (f : forall a, P 
(e a)) (a : α) : (piCongrLeft P e) f (e a) = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_fin_nat_prod_eq_prod`：integral_fin_nat_prod_eq_pr
od {n : Nat} {E : Fin n -> Type*} {mE : forall i, MeasurableSpace (E i)} {μ : (i
 : Fin n) -> Measure (E i)} [fora…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of **Fubini's theorem** with the variables indexed by a general finite
 type.
-/
theorem integral_fintype_prod_eq_prod {E : ι → Type*} (f : (i : ι) → E i → 𝕜)
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫ x, f i x ∂(μ i) := by
  let e := (equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).integral_comp']
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
    MeasureTheory.integral_fin_nat_prod_eq_prod]

/-- A version of **Fubini's theorem** with the variables indexed by a general finite type. -/
/-
**MeasureTheory.integral_fintype_prod_volume_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：integral_fintype_prod_volume_eq_prod {E : ι -> Type*} (f : (i : ι) -> E i 
-> 𝕜) [forall i, MeasureSpace (E i)] [forall i, SigmaFinite (volume : Measure (E
 i))] : ∫ x : (i : ι) -> E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x
参数：f : (i : ι) -> E i -> 𝕜；E i；volume : Measure (E i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_fintype_prod_eq_prod`：integral_fintype_prod_eq_pr
od {E : ι -> Type*} (f : (i : ι) -> E i -> 𝕜) {mE : forall i, MeasurableSpace (E
 i)} {μ : (i : ι) -> Measure (E i…

--- 原说明 ---
A version of **Fubini's theorem** with the variables indexed by a general finite
 type.
-/
theorem integral_fintype_prod_volume_eq_prod {E : ι → Type*} (f : (i : ι) → E i → 𝕜)
    [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))] :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x := integral_fintype_prod_eq_prod _
/-
**MeasureTheory.integral_fintype_prod_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_fintype_prod_eq_pow {E : Type*} (f : E -> 𝕜) {mE : MeasurableSpac
e E} {μ : Measure E} [SigmaFinite μ] : ∫ x : ι -> E, ∏ i, f (x i) ∂(Measure.pi (
fun _ => μ)) = (∫ x, f x ∂μ) ^ (card ι)
参数：f : E -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_fintype_prod_eq_prod`：integral_fintype_prod_eq_pr
od {E : ι -> Type*} (f : (i : ι) -> E i -> 𝕜) {mE : forall i, MeasurableSpace (E
 i)} {μ : (i : ι) -> Measure (E i…
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card.eq_1`：∀ (α : Type u_4) [inst : Fintype α], Fintype.card α =
 Finset.univ.card
-/
theorem integral_fintype_prod_eq_pow {E : Type*} (f : E → 𝕜) {mE : MeasurableSpace E}
    {μ : Measure E} [SigmaFinite μ] :
    ∫ x : ι → E, ∏ i, f (x i) ∂(Measure.pi (fun _ ↦ μ)) = (∫ x, f x ∂μ) ^ (card ι) := by
  rw [integral_fintype_prod_eq_prod, Finset.prod_const, card]
/-
**MeasureTheory.integral_fintype_prod_volume_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：integral_fintype_prod_volume_eq_pow {E : Type*} (f : E -> 𝕜) [MeasureSpace
 E] [SigmaFinite (volume : Measure E)] : ∫ x : ι -> E, ∏ i, f (x i) = (∫ x, f x)
 ^ (card ι)
参数：f : E -> 𝕜；volume : Measure E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_fintype_prod_eq_pow`：integral_fintype_prod_eq_pow
 {E : Type*} (f : E -> 𝕜) {mE : MeasurableSpace E} {μ : Measure E} [SigmaFinite 
μ] : ∫ x : ι -> E, ∏ i, f (x i) …
-/
theorem integral_fintype_prod_volume_eq_pow {E : Type*} (f : E → 𝕜)
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : ι → E, ∏ i, f (x i) = (∫ x, f x) ^ (card ι) := integral_fintype_prod_eq_pow _

variable {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)}
    {E : Type*} [NormedAddCommGroup E]
/-
**MeasureTheory.integrable_comp_eval** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_comp_eval [forall i, IsFiniteMeasure (μ i)] {i : ι} {f : X i ->
 E} (hf : Integrable f (μ i)) : Integrable (fun x => f (x i)) (Measure.pi μ)
参数：μ i；hf : Integrable f (μ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.comp_measurable`：∀ {α : Type u_1} {ε : Type u_5
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace
 ε]   [inst_1 : ContinuousENor…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.pi_map_eval`：pi_map_eval [DecidableEq ι] (i : ι) :
 (Measure.pi μ).map (Function.eval i) = (∏ j in Finset.univ.erase i, μ j Set.uni
v) • (μ i)
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Integrable.smul_measure`：∀ {α : Type u_1} {m : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]
   [inst_1 : ESeminormedAdd…
· 使用引理 `ENNReal.prod_ne_top`：prod_ne_top (h : forall a in s, f a != ∞) : ∏ a in 
s, f a != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma integrable_comp_eval [∀ i, IsFiniteMeasure (μ i)] {i : ι} {f : X i → E}
    (hf : Integrable f (μ i)) :
    Integrable (fun x ↦ f (x i)) (Measure.pi μ) := by
  refine Integrable.comp_measurable ?_ (by fun_prop)
  classical
  rw [Measure.pi_map_eval]
  exact hf.smul_measure <| ENNReal.prod_ne_top (by finiteness)
/-
**MeasureTheory.integrable_eval** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_eval [forall i, NormedAddCommGroup (X i)] [forall i, IsFiniteMe
asure (μ i)] {i : ι} (h : Integrable id (μ i)) : Integrable (fun x => x i) (Meas
ure.pi μ)
参数：X i；μ i；h : Integrable id (μ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integrable_comp_eval`：integrable_comp_eval [forall i, IsFi
niteMeasure (μ i)] {i : ι} {f : X i -> E} (hf : Integrable f (μ i)) : Integrable
 (fun x => f (x i)) (Mea…
-/
lemma integrable_eval [∀ i, NormedAddCommGroup (X i)] [∀ i, IsFiniteMeasure (μ i)] {i : ι}
    (h : Integrable id (μ i)) :
    Integrable (fun x ↦ x i) (Measure.pi μ) :=
  integrable_comp_eval h
/-
**MeasureTheory.integral_comp_eval** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_comp_eval [NormedSpace Real E] [forall i, IsProbabilityMeasure (μ
 i)] {i : ι} {f : X i -> E} (hf : AEStronglyMeasurable f (μ i)) : ∫ x : Π i, X i
, f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i
参数：μ i；hf : AEStronglyMeasurable f (μ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.measurePreserving_eval`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma integral_comp_eval [NormedSpace ℝ E] [∀ i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i → E}
    (hf : AEStronglyMeasurable f (μ i)) :
    ∫ x : Π i, X i, f (x i) ∂Measure.pi μ = ∫ x, f x ∂μ i := by
  rw [← (measurePreserving_eval μ i).map_eq, integral_map]
  · exact Measurable.aemeasurable (by fun_prop)
  · rwa [(measurePreserving_eval μ i).map_eq]
/-
**MeasureTheory.integral_eval** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_eval [forall i, NormedAddCommGroup (X i)] [forall i, NormedSpace 
Real (X i)] [forall i, IsProbabilityMeasure (μ i)] {i : ι} [OpensMeasurableSpace
 (X i)] [SecondCountableTopology (X i)] : ∫ x, x i ∂Measure.pi μ = ∫ x, x ∂μ i
参数：X i；X i；μ i；X i；X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_comp_eval`：integral_comp_eval [NormedSpace Real E
] [forall i, IsProbabilityMeasure (μ i)] {i : ι} {f : X i -> E} (hf : AEStrongly
Measurable f (μ i)) : …
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
lemma integral_eval [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    [∀ i, IsProbabilityMeasure (μ i)] {i : ι} [OpensMeasurableSpace (X i)]
    [SecondCountableTopology (X i)] :
    ∫ x, x i ∂Measure.pi μ = ∫ x, x ∂μ i :=
  integral_comp_eval aestronglyMeasurable_id

end MeasureTheory

