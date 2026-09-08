/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Topology.Separation.Basic

/-!
# Pointwise convergence of indicator functions

In this file, we prove the equivalence of three different ways to phrase that the indicator
functions of sets converge pointwise.

## Main results

For `A` a set, `(Asᵢ)` an indexed collection of sets, under mild conditions, the following are
equivalent:

(a) the indicator functions of `Asᵢ` tend to the indicator function of `A` pointwise;

(b) for every `x`, we eventually have that `x ∈ Asᵢ` holds iff `x ∈ A` holds;

(c) `Tendsto As _ <| Filter.pi (pure <| · ∈ A)`.

The results stating these in the case when the indicators take values in a Fréchet space are:
* `tendsto_indicator_const_iff_forall_eventually` is the equivalence (a) ↔ (b);
* `tendsto_indicator_const_iff_tendsto_pi_pure` is the equivalence (a) ↔ (c).

-/

public section


open Filter Topology

variable {α : Type*} {A : Set α}
variable {β : Type*} [Zero β] [TopologicalSpace β]
variable {ι : Type*} (L : Filter ι) {As : ι → Set α}

/-
**tendsto_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_ite {β : Type*} {p : ι -> Prop} [DecidablePred p] {q : Prop} [Deci
dable q] {a b : β} {F G : Filter β} (haG : {a}ᶜ in G) (hbF : {b}ᶜ in F) (haF : p
rincipal {a} <= F) (hbG : principal {b} <= G) : Tendsto (fun i => if p i then a 
else b) L (if q then F else G) ↔ forallᶠ i in L, p i ↔ q
参数：haG : {a}ᶜ in G；hbF : {b}ᶜ in F；haF : principal {a} <= F；hbG : principal {b} 
<= G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
-/
lemma tendsto_ite {β : Type*} {p : ι → Prop} [DecidablePred p] {q : Prop} [Decidable q]
    {a b : β} {F G : Filter β}
    (haG : {a}ᶜ ∈ G) (hbF : {b}ᶜ ∈ F) (haF : principal {a} ≤ F) (hbG : principal {b} ≤ G) :
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) ↔ ∀ᶠ i in L, p i ↔ q := by
  constructor <;> intro h
  · by_cases hq : q
    · simp only [hq, ite_true] at h
      filter_upwards [mem_map.mp (h hbF)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_right_iff, not_forall, exists_prop] at hi
      tauto
    · simp only [hq, ite_false] at h
      filter_upwards [mem_map.mp (h haG)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_left_iff, not_forall, exists_prop] at hi
      tauto
  · have obs : (fun _ ↦ if q then a else b) =ᶠ[L] (fun i ↦ if p i then a else b) := by
      filter_upwards [h] with i hi
      simp only [hi]
    apply Tendsto.congr' obs
    by_cases hq : q
    · simp only [hq, ite_true]
      apply le_trans _ haF
      simp
    · simp only [hq, ite_false]
      apply le_trans _ hbG
      simp only [principal_singleton, le_pure_iff, mem_map, Set.mem_singleton_iff,
        Set.preimage_const_of_mem, univ_mem]
/-
**tendsto_indicator_const_apply_iff_eventually'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_indicator_const_apply_iff_eventually' (b : β) (nhds_b : {0}ᶜ in 𝓝 
b) (nhds_o : {b}ᶜ in 𝓝 0) (x : α) : Tendsto (fun i => (As i).indicator (fun (_ :
 α) => b) x) L (𝓝 (A.indicator (fun (_ : α) => b) x)) ↔ forallᶠ i in L, (x in As
 i ↔ x in A)
参数：b : β；nhds_b : {0}ᶜ in 𝓝 b；nhds_o : {b}ᶜ in 𝓝 0；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendsto_ite`：tendsto_ite {β : Type*} {p : ι -> Prop} [DecidablePred p] {
q : Prop} [Decidable q] {a b : β} {F G : Filter β} (haG : {a}ᶜ in G) (hbF : {b}ᶜ
 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
lemma tendsto_indicator_const_apply_iff_eventually' (b : β)
    (nhds_b : {0}ᶜ ∈ 𝓝 b) (nhds_o : {b}ᶜ ∈ 𝓝 0) (x : α) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b) x) L (𝓝 (A.indicator (fun (_ : α) ↦ b) x))
      ↔ ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  classical
  have heart := @tendsto_ite ι L β (fun i ↦ x ∈ As i) _ (x ∈ A) _ b 0 (𝓝 b) (𝓝 (0 : β))
                nhds_o nhds_b ?_ ?_
  · convert! heart
    by_cases hxA : x ∈ A <;> simp [hxA]
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhds ↦ mem_of_mem_nhds s_nhds
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhds ↦ mem_of_mem_nhds s_nhds
/-
**tendsto_indicator_const_iff_forall_eventually'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_indicator_const_iff_forall_eventually' (b : β) (nhds_b : {0}ᶜ in 𝓝
 b) (nhds_o : {b}ᶜ in 𝓝 0) : Tendsto (fun i => (As i).indicator (fun (_ : α) => 
b)) L (𝓝 (A.indicator (fun (_ : α) => b))) ↔ forall x, forallᶠ i in L, (x in As 
i ↔ x in A)
参数：b : β；nhds_b : {0}ᶜ in 𝓝 b；nhds_o : {b}ᶜ in 𝓝 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用引理 `tendsto_indicator_const_apply_iff_eventually'`：tendsto_indicator_const_a
pply_iff_eventually' (b : β) (nhds_b : {0}ᶜ in 𝓝 b) (nhds_o : {b}ᶜ in 𝓝 0) (x : 
α) : Tendsto (fun i => (As i).indic…
-/
lemma tendsto_indicator_const_iff_forall_eventually'
    (b : β) (nhds_b : {0}ᶜ ∈ 𝓝 b) (nhds_o : {b}ᶜ ∈ 𝓝 0) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ ∀ x, ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  simp_rw [tendsto_pi_nhds]
  apply forall_congr'
  exact tendsto_indicator_const_apply_iff_eventually' L b nhds_b nhds_o

/-- The indicator functions of `Asᵢ` evaluated at `x` tend to the indicator function of `A`
evaluated at `x` if and only if we eventually have the equivalence `x ∈ Asᵢ ↔ x ∈ A`. -/
/-
**tendsto_indicator_const_apply_iff_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {A : Set α} {β : Type u_2} [inst : Zero β] [inst_1 : Topo
logicalSpace β] {ι : Type u_3} (L : Filter ι)   {As : ι → Set α} [T1Space β] (b 
: β) [NeZero b] (x : α),   Filter.Tendsto (fun i => (As i).indicator (fun x => b
) x) L (nhds (A.indicator (fun x => b) x)) ↔     ∀ᶠ (i : ι) in L, x ∈ As i ↔ x ∈
 A
参数：L : Filter ι；b : β；x : α；fun i => (As i).indicator (fun x => b) x；nhds (A.ind
icator (fun x => b) x)；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendsto_indicator_const_apply_iff_eventually'`：tendsto_indicator_const_a
pply_iff_eventually' (b : β) (nhds_b : {0}ᶜ in 𝓝 b) (nhds_o : {b}ᶜ in 𝓝 0) (x : 
α) : Tendsto (fun i => (As i).indic…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0

--- 原说明 ---
The indicator functions of `Asᵢ` evaluated at `x` tend to the indicator function
 of `A`
evaluated at `x` if and only if we eventually have the equivalence `x ∈ Asᵢ ↔ x 
∈ A`.
-/
@[simp] lemma tendsto_indicator_const_apply_iff_eventually [T1Space β] (b : β) [NeZero b]
    (x : α) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b) x) L (𝓝 (A.indicator (fun (_ : α) ↦ b) x))
      ↔ ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  apply tendsto_indicator_const_apply_iff_eventually' _ b
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne, not_false_eq_true]
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm, not_false_eq_true]

/-- The indicator functions of `Asᵢ` tend to the indicator function of `A` pointwise if and only if
for every `x`, we eventually have the equivalence `x ∈ Asᵢ ↔ x ∈ A`. -/
/-
**tendsto_indicator_const_iff_forall_eventually** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {A : Set α} {β : Type u_2} [inst : Zero β] [inst_1 : Topo
logicalSpace β] {ι : Type u_3} (L : Filter ι)   {As : ι → Set α} [T1Space β] (b 
: β) [NeZero b],   Filter.Tendsto (fun i => (As i).indicator fun x => b) L (nhds
 (A.indicator fun x => b)) ↔     ∀ (x : α), ∀ᶠ (i : ι) in L, x ∈ As i ↔ x ∈ A
参数：L : Filter ι；b : β；fun i => (As i).indicator fun x => b；nhds (A.indicator fun
 x => b)；x : α；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendsto_indicator_const_iff_forall_eventually'`：tendsto_indicator_const_
iff_forall_eventually' (b : β) (nhds_b : {0}ᶜ in 𝓝 b) (nhds_o : {b}ᶜ in 𝓝 0) : T
endsto (fun i => (As i).indicator (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0

--- 原说明 ---
The indicator functions of `Asᵢ` tend to the indicator function of `A` pointwise
 if and only if
for every `x`, we eventually have the equivalence `x ∈ Asᵢ ↔ x ∈ A`.
-/
@[simp] lemma tendsto_indicator_const_iff_forall_eventually [T1Space β] (b : β) [NeZero b] :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ ∀ x, ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  apply tendsto_indicator_const_iff_forall_eventually' _ b
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne, not_false_eq_true]
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm, not_false_eq_true]
/-
**tendsto_indicator_const_iff_tendsto_pi_pure'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_indicator_const_iff_tendsto_pi_pure' (b : β) (nhds_b : {0}ᶜ in 𝓝 b
) (nhds_o : {b}ᶜ in 𝓝 0) : Tendsto (fun i => (As i).indicator (fun (_ : α) => b)
) L (𝓝 (A.indicator (fun (_ : α) => b))) ↔ (Tendsto (fun i x => x in As i) L <| 
Filter.pi (pure <| · in A))
参数：b : β；nhds_b : {0}ᶜ in 𝓝 b；nhds_o : {b}ᶜ in 𝓝 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `tendsto_indicator_const_iff_forall_eventually'`：tendsto_indicator_const_
iff_forall_eventually' (b : β) (nhds_b : {0}ᶜ in 𝓝 b) (nhds_o : {b}ᶜ in 𝓝 0) : T
endsto (fun i => (As i).indicator (f…
· 使用定理 `Filter.tendsto_pi`：tendsto_pi {β : Type*} {m : β -> forall i, α i} {l : 
Filter β} : Tendsto m l (pi f) ↔ forall i, Tendsto (fun x => m x i) l (f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma tendsto_indicator_const_iff_tendsto_pi_pure'
    (b : β) (nhds_b : {0}ᶜ ∈ 𝓝 b) (nhds_o : {b}ᶜ ∈ 𝓝 0) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ (Tendsto (fun i x ↦ x ∈ As i) L <| Filter.pi (pure <| · ∈ A)) := by
  rw [tendsto_indicator_const_iff_forall_eventually' _ b nhds_b nhds_o, tendsto_pi]
  simp_rw [tendsto_pure]
  aesop
/-
**tendsto_indicator_const_iff_tendsto_pi_pure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_indicator_const_iff_tendsto_pi_pure [T1Space β] (b : β) [NeZero b]
 : Tendsto (fun i => (As i).indicator (fun (_ : α) => b)) L (𝓝 (A.indicator (fun
 (_ : α) => b))) ↔ (Tendsto (fun i x => x in As i) L <| Filter.pi (pure <| · in 
A))
参数：b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_indicator_const_iff_forall_eventually`：∀ {α : Type u_1} {A : Set
 α} {β : Type u_2} [inst : Zero β] [inst_1 : TopologicalSpace β] {ι : Type u_3} 
(L : Filter ι)   {As : ι → Set α} […
· 使用定理 `Filter.tendsto_pi`：tendsto_pi {β : Type*} {m : β -> forall i, α i} {l : 
Filter β} : Tendsto m l (pi f) ↔ forall i, Tendsto (fun x => m x i) l (f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma tendsto_indicator_const_iff_tendsto_pi_pure [T1Space β] (b : β) [NeZero b] :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ (Tendsto (fun i x ↦ x ∈ As i) L <| Filter.pi (pure <| · ∈ A)) := by
  rw [tendsto_indicator_const_iff_forall_eventually _ b, tendsto_pi]
  simp_rw [tendsto_pure]
  aesop
