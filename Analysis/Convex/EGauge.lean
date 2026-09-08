/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Seminorm
public import Mathlib.GroupTheory.GroupAction.Pointwise

/-!
# The Minkowski functional, normed field version

In this file we define `(egauge 𝕜 s ·)`
to be the Minkowski functional (gauge) of the set `s`
in a topological vector space `E` over a normed field `𝕜`,
as a function `E → ℝ≥0∞`.

It is defined as the infimum of the norms of `c : 𝕜` such that `x ∈ c • s`.
In particular, for `𝕜 = ℝ≥0` this definition gives an `ℝ≥0∞`-valued version of `gauge`
defined in `Mathlib/Analysis/Convex/Gauge.lean`.

This definition can be used to generalize the notion of Fréchet derivative
to maps between topological vector spaces without norms.

Currently, we can't reuse results about `egauge` for `gauge`,
because we lack a theory of normed semifields.
-/

@[expose] public section

open Function Set Filter Metric
open scoped Topology Pointwise ENNReal NNReal

section SMul

/-- The Minkowski functional for vector spaces over normed fields.
Given a set `s` in a vector space over a normed field `𝕜`,
`egauge s` is the functional which sends `x : E`
to the infimum of `‖c‖ₑ` over `c` such that `x` belongs to `s` scaled by `c`.

The definition only requires `𝕜` to have a `ENorm` instance
and `(· • ·) : 𝕜 → E → E` to be defined.
This way the definition applies, e.g., to `𝕜 = ℝ≥0`.
For `𝕜 = ℝ≥0`, the function is equal (up to conversion to `ℝ`)
to the usual Minkowski functional defined in `gauge`. -/
/-
**egauge** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：egauge (𝕜 : Type*) [ENorm 𝕜] {E : Type*} [SMul 𝕜 E] (s : Set E) (x : E) : 
Real>=0∞
参数：𝕜 : Type*；s : Set E；x : E。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Minkowski functional for vector spaces over normed fields.
Given a set `s` in a vector space over a normed field `𝕜`,
`egauge s` is the functional which sends `x : E`
to the infimum of `‖c‖ₑ` over `c` such that `x` belongs to `s` scaled by `c`.

The definition only requires `𝕜` to have a `ENorm` instance
and `(· • ·) : 𝕜 → E → E` to be defined.
This way the definition applies, e.g., to `𝕜 = ℝ≥0`.
For `𝕜 = ℝ≥0`, the function is equal (up to conversion to `ℝ`)
to the usual Minkowski functional defined in `gauge`.
-/
noncomputable def egauge (𝕜 : Type*) [ENorm 𝕜] {E : Type*} [SMul 𝕜 E] (s : Set E) (x : E) : ℝ≥0∞ :=
  ⨅ (c : 𝕜) (_ : x ∈ c • s), ‖c‖ₑ

variable (𝕜 : Type*) [NNNorm 𝕜] {E : Type*} [SMul 𝕜 E] {c : 𝕜} {s t : Set E} {x : E} {r : ℝ≥0∞}
/-
**Set.MapsTo.egauge_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.MapsTo.egauge_le {E' F : Type*} [SMul 𝕜 E'] [FunLike F E E'] [MulActio
nHomClass F 𝕜 E E'] (f : F) {t : Set E'} (h : MapsTo f s t) (x : E) : egauge 𝕜 t
 (f x) <= egauge 𝕜 s x
参数：f : F；h : MapsTo f s t；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `iInf_mono'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Comp
leteLattice α] {f : ι → α} {g : ι' → α},   (∀ (i : ι), ∃ i', g i' ≤ f i) → iInf 
…
· 使用定理 `Set.MapsTo.smul_set`：Set.MapsTo.smul_set {f : F} {s : Set α} {t : Set β}
 (hst : MapsTo f s t) (c : M) : MapsTo f (c • s) (c • t)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma Set.MapsTo.egauge_le {E' F : Type*} [SMul 𝕜 E'] [FunLike F E E'] [MulActionHomClass F 𝕜 E E']
    (f : F) {t : Set E'} (h : MapsTo f s t) (x : E) : egauge 𝕜 t (f x) ≤ egauge 𝕜 s x :=
  iInf_mono fun c ↦ iInf_mono' fun hc ↦ ⟨h.smul_set c hc, le_rfl⟩

@[mono, gcongr]
/-
**egauge_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_anti (h : s subseteq t) (x : E) : egauge 𝕜 t x <= egauge 𝕜 s x
参数：h : s subseteq t；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.MapsTo.egauge_le`：Set.MapsTo.egauge_le {E' F : Type*} [SMul 𝕜 E'] [F
unLike F E E'] [MulActionHomClass F 𝕜 E E'] (f : F) {t : Set E'} (h : MapsTo f s
 t) (x : E…
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
-/
lemma egauge_anti (h : s ⊆ t) (x : E) : egauge 𝕜 t x ≤ egauge 𝕜 s x :=
  MapsTo.egauge_le _ (MulActionHom.id ..) h _
/-
**egauge_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (𝕜 : Type u_1) [inst : NNNorm 𝕜] {E : Type u_2} [inst_1 : SMul 𝕜 E] (x :
 E), egauge 𝕜 ∅ x = ⊤
参数：𝕜 : Type u_1；x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma egauge_empty (x : E) : egauge 𝕜 ∅ x = ∞ := by simp [egauge]

variable {𝕜}
/-
**egauge_le_of_mem_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_le_of_mem_smul (h : x in c • s) : egauge 𝕜 s x <= ‖c‖ₑ
参数：h : x in c • s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
-/
lemma egauge_le_of_mem_smul (h : x ∈ c • s) : egauge 𝕜 s x ≤ ‖c‖ₑ := iInf₂_le c h
/-
**le_egauge_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_egauge_iff : r <= egauge 𝕜 s x ↔ forall c : 𝕜, x in c • s -> r <= ‖c‖ₑ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂_iff`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst :
 CompleteLattice α] {a : α} {f : (i : ι) → κ i → α},   a ≤ ⨅ i, ⨅ j, f i j ↔ ∀ (
i …
-/
lemma le_egauge_iff : r ≤ egauge 𝕜 s x ↔ ∀ c : 𝕜, x ∈ c • s → r ≤ ‖c‖ₑ := le_iInf₂_iff
/-
**egauge_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_eq_top : egauge 𝕜 s x = ∞ ↔ forall c : 𝕜, x ∉ c • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma egauge_eq_top : egauge 𝕜 s x = ∞ ↔ ∀ c : 𝕜, x ∉ c • s := by simp [egauge]
/-
**egauge_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_lt_iff : egauge 𝕜 s x < r ↔ exists c : 𝕜, x in c • s ∧ ‖c‖ₑ < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma egauge_lt_iff : egauge 𝕜 s x < r ↔ ∃ c : 𝕜, x ∈ c • s ∧ ‖c‖ₑ < r := by
  simp [egauge, iInf_lt_iff]
/-
**egauge_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_union (s t : Set E) (x : E) : egauge 𝕜 (s union t) x = egauge 𝕜 s x
 ⊓ egauge 𝕜 t x
参数：s t : Set E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Set.smul_set_union`：smul_set_union : a • (t₁ union t₂) = a • t₁ union a 
• t₂
· 使用定理 `iInf_or`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : p
 ∨ q → α},   ⨅ (x : p ∨ q), s x = (⨅ (i : p), s ⋯) ⊓ ⨅ (j : q), s ⋯
· 使用定理 `iInf_inf_eq`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f g : ι → α}, ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ ⨅ x, g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma egauge_union (s t : Set E) (x : E) : egauge 𝕜 (s ∪ t) x = egauge 𝕜 s x ⊓ egauge 𝕜 t x := by
  unfold egauge
  simp [smul_set_union, iInf_or, iInf_inf_eq]
/-
**le_egauge_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_egauge_inter (s t : Set E) (x : E) : egauge 𝕜 s x ⊔ egauge 𝕜 t x <= ega
uge 𝕜 (s inter t) x
参数：s t : Set E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用引理 `egauge_anti`：egauge_anti (h : s subseteq t) (x : E) : egauge 𝕜 t x <= eg
auge 𝕜 s x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma le_egauge_inter (s t : Set E) (x : E) :
    egauge 𝕜 s x ⊔ egauge 𝕜 t x ≤ egauge 𝕜 (s ∩ t) x :=
  max_le (egauge_anti _ inter_subset_left _) (egauge_anti _ inter_subset_right _)
/-
**le_egauge_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_egauge_pi {ι : Type*} {E : ι -> Type*} [forall i, SMul 𝕜 (E i)] {I : Se
t ι} {i : ι} (hi : i in I) (s : forall i, Set (E i)) (x : forall i, E i) : egaug
e 𝕜 (s i) (x i) <= egauge 𝕜 (I.pi s) x
参数：E i；hi : i in I；s : forall i, Set (E i)；x : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.MapsTo.egauge_le`：Set.MapsTo.egauge_le {E' F : Type*} [SMul 𝕜 E'] [F
unLike F E E'] [MulActionHomClass F 𝕜 E E'] (f : F) {t : Set E'} (h : MapsTo f s
 t) (x : E…
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
-/
lemma le_egauge_pi {ι : Type*} {E : ι → Type*} [∀ i, SMul 𝕜 (E i)] {I : Set ι} {i : ι}
    (hi : i ∈ I) (s : ∀ i, Set (E i)) (x : ∀ i, E i) :
    egauge 𝕜 (s i) (x i) ≤ egauge 𝕜 (I.pi s) x :=
  MapsTo.egauge_le _ (Pi.evalMulActionHom i) (fun x hx ↦ by exact hx i hi) _

variable {F : Type*} [SMul 𝕜 F]
/-
**le_egauge_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_egauge_prod (s : Set E) (t : Set F) (a : E) (b : F) : max (egauge 𝕜 s a
) (egauge 𝕜 t b) <= egauge 𝕜 (s ×ˢ t) (a, b)
参数：s : Set E；t : Set F；a : E；b : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用引理 `Set.MapsTo.egauge_le`：Set.MapsTo.egauge_le {E' F : Type*} [SMul 𝕜 E'] [F
unLike F E E'] [MulActionHomClass F 𝕜 E E'] (f : F) {t : Set E'} (h : MapsTo f s
 t) (x : E…
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用引理 `Set.mapsTo_fst_prod`：mapsTo_fst_prod {s : Set α} {t : Set β} : MapsTo Pr
od.fst (s ×ˢ t) s
· 使用引理 `Set.mapsTo_snd_prod`：mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Pr
od.snd (s ×ˢ t) t
-/
lemma le_egauge_prod (s : Set E) (t : Set F) (a : E) (b : F) :
    max (egauge 𝕜 s a) (egauge 𝕜 t b) ≤ egauge 𝕜 (s ×ˢ t) (a, b) :=
  max_le (mapsTo_fst_prod.egauge_le 𝕜 (MulActionHom.fst 𝕜 E F) (a, b))
    (MapsTo.egauge_le 𝕜 (MulActionHom.snd 𝕜 E F) mapsTo_snd_prod (a, b))

end SMul

section SMulZero

variable (𝕜 : Type*) [NNNorm 𝕜] [Nonempty 𝕜] {E : Type*} [Zero E] [SMulZeroClass 𝕜 E] {x : E}

/-
**egauge_zero_left_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (𝕜 : Type u_1) [inst : NNNorm 𝕜] [Nonempty 𝕜] {E : Type u_2} [inst_2 : Z
ero E] [inst_3 : SMulZeroClass 𝕜 E] {x : E},   egauge 𝕜 0 x = ⊤ ↔ x ≠ 0
参数：𝕜 : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma egauge_zero_left_eq_top : egauge 𝕜 0 x = ∞ ↔ x ≠ 0 := by
  simp [egauge_eq_top]

@[simp] alias ⟨_, egauge_zero_left⟩ := egauge_zero_left_eq_top

end SMulZero

section NormedDivisionRing

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    {c : 𝕜} {s : Set E} {x : E}

/-- If `c • x ∈ s` and `c ≠ 0`, then `egauge 𝕜 s x` is at most `(‖c‖₊⁻¹ : ℝ≥0)`.

See also `egauge_le_of_smul_mem`. -/
/-
**egauge_le_of_smul_mem_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_le_of_smul_mem_of_ne (h : c • x in s) (hc : c != 0) : egauge 𝕜 s x 
<= (‖c‖₊⁻¹ : Real>=0)
参数：h : c • x in s；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nnnorm_inv`：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
· 使用引理 `egauge_le_of_mem_smul`：egauge_le_of_mem_smul (h : x in c • s) : egauge 𝕜
 s x <= ‖c‖ₑ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mem_inv_smul_set_iff₀`：mem_inv_smul_set_iff₀ (ha : a != 0) (A : Set 
β) (x : β) : x in a⁻¹ • A ↔ a • x in A

--- 原说明 ---
If `c • x ∈ s` and `c ≠ 0`, then `egauge 𝕜 s x` is at most `(‖c‖₊⁻¹ : ℝ≥0)`.

See also `egauge_le_of_smul_mem`.
-/
lemma egauge_le_of_smul_mem_of_ne (h : c • x ∈ s) (hc : c ≠ 0) : egauge 𝕜 s x ≤ (‖c‖₊⁻¹ : ℝ≥0) := by
  rw [← nnnorm_inv]
  exact egauge_le_of_mem_smul <| (mem_inv_smul_set_iff₀ hc _ _).2 h

/-- If `c • x ∈ s`, then `egauge 𝕜 s x` is at most `‖c‖ₑ⁻¹`.

See also `egauge_le_of_smul_mem_of_ne`. -/
/-
**egauge_le_of_smul_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_le_of_smul_mem (h : c • x in s) : egauge 𝕜 s x <= ‖c‖ₑ⁻¹
参数：h : c • x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `egauge_le_of_smul_mem_of_ne`：egauge_le_of_smul_mem_of_ne (h : c • x in s
) (hc : c != 0) : egauge 𝕜 s x <= (‖c‖₊⁻¹ : Real>=0)
· 使用定理 `ENNReal.coe_inv_le`：coe_inv_le : (↑r⁻¹ : Real>=0∞) <= (↑r)⁻¹

--- 原说明 ---
If `c • x ∈ s`, then `egauge 𝕜 s x` is at most `‖c‖ₑ⁻¹`.

See also `egauge_le_of_smul_mem_of_ne`.
-/
lemma egauge_le_of_smul_mem (h : c • x ∈ s) : egauge 𝕜 s x ≤ ‖c‖ₑ⁻¹ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (egauge_le_of_smul_mem_of_ne h hc).trans ENNReal.coe_inv_le
/-
**mem_smul_of_egauge_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_smul_of_egauge_lt (hs : Balanced 𝕜 s) (hc : egauge 𝕜 s x < ‖c‖ₑ) : x i
n c • s
参数：hs : Balanced 𝕜 s；hc : egauge 𝕜 s x < ‖c‖ₑ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `egauge_lt_iff`：egauge_lt_iff : egauge 𝕜 s x < r ↔ exists c : 𝕜, x in c •
 s ∧ ‖c‖ₑ < r
· 使用定理 `Balanced.smul_mono`：Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} (h : 
‖a‖ <= ‖b‖) : a • s subseteq b • s
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma mem_smul_of_egauge_lt (hs : Balanced 𝕜 s) (hc : egauge 𝕜 s x < ‖c‖ₑ) : x ∈ c • s :=
  let ⟨a, hxa, ha⟩ := egauge_lt_iff.1 hc
  hs.smul_mono (by simpa [enorm] using! ha.le) hxa
/-
**mem_of_egauge_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_of_egauge_lt_one (hs : Balanced 𝕜 s) (hx : egauge 𝕜 s x < 1) : x in s
参数：hs : Balanced 𝕜 s；hx : egauge 𝕜 s x < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mem_smul_of_egauge_lt`：mem_smul_of_egauge_lt (hs : Balanced 𝕜 s) (hc : e
gauge 𝕜 s x < ‖c‖ₑ) : x in c • s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma mem_of_egauge_lt_one (hs : Balanced 𝕜 s) (hx : egauge 𝕜 s x < 1) : x ∈ s :=
  one_smul 𝕜 s ▸ mem_smul_of_egauge_lt hs (by simpa)
/-
**egauge_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_eq_zero_iff : egauge 𝕜 s x = 0 ↔ existsᶠ c : 𝕜 in 𝓝 0, x in c • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `iInf₂_eq_bot`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst :
 CompleteLinearOrder α] (f : (i : ι) → κ i → α),   ⨅ i, ⨅ j, f i j = ⊥ ↔ ∀ (b : 
α)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma egauge_eq_zero_iff : egauge 𝕜 s x = 0 ↔ ∃ᶠ c : 𝕜 in 𝓝 0, x ∈ c • s := by
  refine (iInf₂_eq_bot _).trans ?_
  rw [(nhds_basis_uniformity uniformity_basis_edist).frequently_iff]
  simp [and_comm]

@[simp]
/-
**egauge_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_univ [(𝓝[!=] (0 : 𝕜)).NeBot] : egauge 𝕜 univ x = 0
参数：𝓝[!=] (0 : 𝕜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `egauge_eq_zero_iff`：egauge_eq_zero_iff : egauge 𝕜 s x = 0 ↔ existsᶠ c : 
𝕜 in 𝓝 0, x in c • s
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.frequently_iff_neBot`：frequently_iff_neBot {l : Filter α} {p : α 
-> Prop} : (existsᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x})
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.smul_set_univ₀`：smul_set_univ₀ (ha : a != 0) : a • (univ : Set β) = 
univ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma egauge_univ [(𝓝[≠] (0 : 𝕜)).NeBot] : egauge 𝕜 univ x = 0 := by
  rw [egauge_eq_zero_iff]
  refine (frequently_iff_neBot.2 ‹_›).mono fun c hc ↦ ?_
  simp_all [smul_set_univ₀]

variable (𝕜)

@[simp]
/-
**egauge_zero_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_zero_right (hs : s.Nonempty) : egauge 𝕜 s 0 = 0
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `egauge_le_of_mem_smul`：egauge_le_of_mem_smul (h : x in c • s) : egauge 𝕜
 s x <= ‖c‖ₑ
-/
lemma egauge_zero_right (hs : s.Nonempty) : egauge 𝕜 s 0 = 0 := by
  have : 0 ∈ (0 : 𝕜) • s := by simp [zero_smul_set hs]
  simpa using egauge_le_of_mem_smul this
/-
**egauge_zero_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_zero_zero : egauge 𝕜 (0 : Set E) 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `egauge_zero_right`：egauge_zero_right (hs : s.Nonempty) : egauge 𝕜 s 0 = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma egauge_zero_zero : egauge 𝕜 (0 : Set E) 0 = 0 := by simp
/-
**egauge_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_le_one (h : x in s) : egauge 𝕜 s x <= 1
参数：h : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `egauge_le_of_mem_smul`：egauge_le_of_mem_smul (h : x in c • s) : egauge 𝕜
 s x <= ‖c‖ₑ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma egauge_le_one (h : x ∈ s) : egauge 𝕜 s x ≤ 1 := by
  rw [← one_smul 𝕜 s] at h
  simpa using egauge_le_of_mem_smul h

variable {𝕜}
/-
**le_egauge_of_forall_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_egauge_of_forall_ne_zero [(𝓝[!=] (0 : 𝕜)).NeBot] {r : Real>=0∞} (hs₀ : 
0 in s) (h : forall c : 𝕜, c != 0 -> x in c • s -> r <= ‖c‖ₑ) : r <= egauge 𝕜 s 
x
参数：𝓝[!=] (0 : 𝕜)；hs₀ : 0 in s；h : forall c : 𝕜, c != 0 -> x in c • s -> r <= ‖c‖
ₑ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_egauge_iff`：le_egauge_iff : r <= egauge 𝕜 s x ↔ forall c : 𝕜, x in c 
• s -> r <= ‖c‖ₑ
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_zero`：∀ {α : Type u_2} [inst : Zero α] {a : α}, a ∈ 0 ↔ a = 0
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用引理 `Set.zero_smul_set_subset`：zero_smul_set_subset (s : Set β) : (0 : α) • s
 subseteq 0
-/
lemma le_egauge_of_forall_ne_zero [(𝓝[≠] (0 : 𝕜)).NeBot] {r : ℝ≥0∞}
    (hs₀ : 0 ∈ s) (h : ∀ c : 𝕜, c ≠ 0 → x ∈ c • s → r ≤ ‖c‖ₑ) : r ≤ egauge 𝕜 s x := by
  rw [le_egauge_iff]
  intro c hc
  rcases ne_or_eq c 0 with hc₀ | rfl
  · exact h c hc₀ hc
  obtain rfl : x = 0 := by
    grw [zero_smul_set_subset, Set.mem_zero] at hc
    exact hc
  apply le_of_forall_gt
  intro b hb
  rcases Filter.nonempty_of_mem <|
    inter_mem_nhdsWithin {(0 : 𝕜)}ᶜ (Metric.eball_mem_nhds 0 (by simpa using hb))
    with ⟨c, hc₀, hcb⟩
  exact (h c (by simpa using hc₀) ⟨_, hs₀, by simp⟩).trans_lt (by simpa using hcb)
/-
**le_egauge_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_egauge_smul_left (c : 𝕜) (s : Set E) (x : E) : egauge 𝕜 s x / ‖c‖ₑ <= e
gauge 𝕜 (c • s) x
参数：c : 𝕜；s : Set E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `ENNReal.div_le_of_le_mul`：div_le_of_le_mul (h : a <= b * c) : a / c <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `enorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 : 
Mul α] [NormMulClass α] (a b : α), ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `egauge_le_of_mem_smul`：egauge_le_of_mem_smul (h : x in c • s) : egauge 𝕜
 s x <= ‖c‖ₑ
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
lemma le_egauge_smul_left (c : 𝕜) (s : Set E) (x : E) :
    egauge 𝕜 s x / ‖c‖ₑ ≤ egauge 𝕜 (c • s) x := by
  simp_rw [le_egauge_iff, smul_smul]
  rintro a ⟨x, hx, rfl⟩
  apply ENNReal.div_le_of_le_mul
  rw [← enorm_mul]
  exact egauge_le_of_mem_smul <| smul_mem_smul_set hx
/-
**egauge_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_smul_left (hc : c != 0) (s : Set E) (x : E) : egauge 𝕜 (c • s) x = 
egauge 𝕜 s x / ‖c‖ₑ
参数：hc : c != 0；s : Set E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `enorm_inv`：enorm_inv {a : α} (ha : a != 0) : ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `le_egauge_smul_left`：le_egauge_smul_left (c : 𝕜) (s : Set E) (x : E) : e
gauge 𝕜 s x / ‖c‖ₑ <= egauge 𝕜 (c • s) x
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
lemma egauge_smul_left (hc : c ≠ 0) (s : Set E) (x : E) :
    egauge 𝕜 (c • s) x = egauge 𝕜 s x / ‖c‖ₑ := by
  refine le_antisymm ?_ (le_egauge_smul_left _ _ _)
  rw [ENNReal.le_div_iff_mul_le (by simp [*]) (by simp)]
  calc
    egauge 𝕜 (c • s) x * ‖c‖ₑ = egauge 𝕜 (c • s) x / ‖c⁻¹‖ₑ := by
      rw [enorm_inv (by simpa), div_eq_mul_inv, inv_inv]
    _ ≤ egauge 𝕜 (c⁻¹ • c • s) x := le_egauge_smul_left _ _ _
    _ = egauge 𝕜 s x := by rw [inv_smul_smul₀ hc]
/-
**le_egauge_smul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_egauge_smul_right (c : 𝕜) (s : Set E) (x : E) : ‖c‖ₑ * egauge 𝕜 s x <= 
egauge 𝕜 s (c • x)
参数：c : 𝕜；s : Set E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_egauge_iff`：le_egauge_iff : r <= egauge 𝕜 s x ↔ forall c : 𝕜, x in c 
• s -> r <= ‖c‖ₑ
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_le_of_le_div'`：mul_le_of_le_div' (h : a <= b / c) : c * a <=
 b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `nnnorm_inv`：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `egauge_le_of_mem_smul`：egauge_le_of_mem_smul (h : x in c • s) : egauge 𝕜
 s x <= ‖c‖ₑ
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ENNReal.coe_div_le`：coe_div_le : ↑(p / r) <= (p / r : Real>=0∞)
-/
lemma le_egauge_smul_right (c : 𝕜) (s : Set E) (x : E) :
    ‖c‖ₑ * egauge 𝕜 s x ≤ egauge 𝕜 s (c • x) := by
  rw [le_egauge_iff]
  rintro a ⟨y, hy, hxy⟩
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · refine ENNReal.mul_le_of_le_div' <| le_trans ?_ ENNReal.coe_div_le
    rw [div_eq_inv_mul, ← nnnorm_inv, ← nnnorm_mul]
    refine egauge_le_of_mem_smul ⟨y, hy, ?_⟩
    simp only [mul_smul, hxy, inv_smul_smul₀ hc]
/-
**egauge_smul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_smul_right (h : c = 0 -> s.Nonempty) (x : E) : egauge 𝕜 s (c • x) =
 ‖c‖ₑ * egauge 𝕜 s x
参数：h : c = 0 -> s.Nonempty；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `egauge_zero_right`：egauge_zero_right (hs : s.Nonempty) : egauge 𝕜 s 0 = 
0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.div_le_iff_le_mul`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ 
c ≠ 0 → (a / b ≤ c ↔ a ≤ c * b)
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用引理 `enorm_inv`：enorm_inv {a : α} (ha : a != 0) : ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `le_egauge_smul_right`：le_egauge_smul_right (c : 𝕜) (s : Set E) (x : E) :
 ‖c‖ₑ * egauge 𝕜 s x <= egauge 𝕜 s (c • x)
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
lemma egauge_smul_right (h : c = 0 → s.Nonempty) (x : E) :
    egauge 𝕜 s (c • x) = ‖c‖ₑ * egauge 𝕜 s x := by
  refine le_antisymm ?_ (le_egauge_smul_right c s x)
  rcases eq_or_ne c 0 with rfl | hc
  · simp [egauge_zero_right _ (h rfl)]
  · rw [mul_comm, ← ENNReal.div_le_iff_le_mul (.inl <| by simpa) (.inl enorm_ne_top),
      ENNReal.div_eq_inv_mul, ← enorm_inv (by simpa)]
    refine (le_egauge_smul_right _ _ _).trans_eq ?_
    rw [inv_smul_smul₀ hc]

/-- The extended gauge of a point `(a, b)` with respect to the product of balanced sets `U` and `V`
is equal to the maximum of the extended gauges of `a` with respect to `U`
and `b` with respect to `V`.
-/
/-
**egauge_prod_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：egauge_prod_mk {F : Type*} [AddCommGroup F] [Module 𝕜 F] {U : Set E} {V : 
Set F} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a : E) (b : F) : egauge 𝕜 (U ×ˢ 
V) (a, b) = max (egauge 𝕜 U a) (egauge 𝕜 V b)
参数：hU : Balanced 𝕜 U；hV : Balanced 𝕜 V；a : E；b : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.smul_set_prod`：smul_set_prod {M α : Type*} [SMul M α] [SMul M β] (c 
: M) (s : Set α) (t : Set β) : c • (s ×ˢ t) = (c • s) ×ˢ (c • t)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Balanced.smul_mono`：Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} (h : 
‖a‖ <= ‖b‖) : a • s subseteq b • s
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `le_egauge_prod`：le_egauge_prod (s : Set E) (t : Set F) (a : E) (b : F) :
 max (egauge 𝕜 s a) (egauge 𝕜 t b) <= egauge 𝕜 (s ×ˢ t) (a, b)

--- 原说明 ---
The extended gauge of a point `(a, b)` with respect to the product of balanced s
ets `U` and `V`
is equal to the maximum of the extended gauges of `a` with respect to `U`
and `b` with respect to `V`.
-/
theorem egauge_prod_mk {F : Type*} [AddCommGroup F] [Module 𝕜 F] {U : Set E} {V : Set F}
    (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a : E) (b : F) :
    egauge 𝕜 (U ×ˢ V) (a, b) = max (egauge 𝕜 U a) (egauge 𝕜 V b) := by
  refine le_antisymm (le_of_forall_gt fun r hr ↦ ?_) (le_egauge_prod _ _ _ _)
  simp only [max_lt_iff, egauge_lt_iff, smul_set_prod] at hr ⊢
  rcases hr with ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩
  cases le_total ‖x‖ ‖y‖ with
  | inl hle => exact ⟨y, ⟨hU.smul_mono hle hx, hy⟩, hyr⟩
  | inr hle => exact ⟨x, ⟨hx, hV.smul_mono hle hy⟩, hxr⟩
/-
**egauge_add_add_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：egauge_add_add_le {U V : Set E} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a
 b : E) : egauge 𝕜 (U + V) (a + b) <= max (egauge 𝕜 U a) (egauge 𝕜 V b)
参数：hU : Balanced 𝕜 U；hV : Balanced 𝕜 V；a b : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `egauge_prod_mk`：egauge_prod_mk {F : Type*} [AddCommGroup F] [Module 𝕜 F]
 {U : Set E} {V : Set F} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a : E) (b : F)
 : e…
· 使用定理 `Set.add_image_prod`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, (fun 
x => x.1 + x.2) '' s ×ˢ t = s + t
· 使用引理 `Set.MapsTo.egauge_le`：Set.MapsTo.egauge_le {E' F : Type*} [SMul 𝕜 E'] [F
unLike F E E'] [MulActionHomClass F 𝕜 E E'] (f : F) {t : Set E'} (h : MapsTo f s
 t) (x : E…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem egauge_add_add_le {U V : Set E} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a b : E) :
    egauge 𝕜 (U + V) (a + b) ≤ max (egauge 𝕜 U a) (egauge 𝕜 V b) := by
  rw [← egauge_prod_mk hU hV a b, ← add_image_prod]
  exact MapsTo.egauge_le 𝕜 (LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E) (mapsTo_image _ _) (a, b)

end NormedDivisionRing

section Pi

variable {𝕜 : Type*} {ι : Type*} {E : ι → Type*}
variable [NormedDivisionRing 𝕜] [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]

/-- The extended gauge of a point `x` in an indexed product
with respect to a product of finitely many balanced sets `U i`, `i ∈ I`,
(and the whole spaces for the other indices)
is the supremum of the extended gauges of the components of `x`
with respect to the corresponding balanced set.

This version assumes the following technical condition:
- either `I` is the universal set;
- or one of `x i`, `i ∈ I`, is nonzero;
- or `𝕜` is nontrivially normed.
-/
/-
**egauge_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：egauge_pi' {I : Set ι} (hI : I.Finite) {U : forall i, Set (E i)} (hU : for
all i in I, Balanced 𝕜 (U i)) (x : forall i, E i) (hI₀ : I = univ ∨ (exists i in
 I, x i != 0) ∨ (𝓝[!=] (0 : 𝕜)).NeBot) : egauge 𝕜 (I.pi U) x = ⨆ i in I, egauge 
𝕜 (U i) (x i)
参数：hI : I.Finite；E i；hU : forall i in I, Balanced 𝕜 (U i)；x : forall i, E i；hI₀ 
: I = univ ∨ (exists i in I, x i != 0) ∨ (𝓝[!=] (0 : 𝕜)).NeBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `egauge_lt_iff`：egauge_lt_iff : egauge 𝕜 s x < r ↔ exists c : 𝕜, x in c •
 s ∧ ‖c‖ₑ < r
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `LT.lt.bot_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → ⊥ < a
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `exists_enorm_lt`：∀ (E : Type u_8) [inst : TopologicalSpace E] [inst_1 : 
ESeminormedAddMonoid E] [hbot : (nhdsWithin 0 {0}ᶜ).NeBot]   {c : ENNReal}, c ≠ 
0 → ∃…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The extended gauge of a point `x` in an indexed product
with respect to a product of finitely many balanced sets `U i`, `i ∈ I`,
(and the whole spaces for the other indices)
is the supremum of the extended gauges of the components of `x`
with respect to the corresponding balanced set.

This version assumes the following technical condition:
- either `I` is the universal set;
- or one of `x i`, `i ∈ I`, is nonzero;
- or `𝕜` is nontrivially normed.
-/
theorem egauge_pi' {I : Set ι} (hI : I.Finite)
    {U : ∀ i, Set (E i)} (hU : ∀ i ∈ I, Balanced 𝕜 (U i))
    (x : ∀ i, E i) (hI₀ : I = univ ∨ (∃ i ∈ I, x i ≠ 0) ∨ (𝓝[≠] (0 : 𝕜)).NeBot) :
    egauge 𝕜 (I.pi U) x = ⨆ i ∈ I, egauge 𝕜 (U i) (x i) := by
  refine le_antisymm ?_ (iSup₂_le fun i hi ↦ le_egauge_pi hi _ _)
  refine le_of_forall_gt fun r hr ↦ ?_
  have : ∀ i ∈ I, ∃ c : 𝕜, x i ∈ c • U i ∧ ‖c‖ₑ < r := fun i hi ↦
    egauge_lt_iff.mp <| (le_iSup₂ i hi).trans_lt hr
  choose! c hc hcr using this
  obtain ⟨c₀, hc₀, hc₀I, hc₀r⟩ :
      ∃ c₀ : 𝕜, (c₀ ≠ 0 ∨ I = univ) ∧ (∀ i ∈ I, ‖c i‖ ≤ ‖c₀‖) ∧ ‖c₀‖ₑ < r := by
    have hr₀ : 0 < r := hr.bot_lt
    rcases I.eq_empty_or_nonempty with rfl | hIne
    · obtain hι | hbot : IsEmpty ι ∨ (𝓝[≠] (0 : 𝕜)).NeBot := by simpa [@eq_comm _ ∅] using hI₀
      · use 0
        simp [@eq_comm _ ∅, hι, hr₀]
      · rcases exists_enorm_lt 𝕜 hr₀.ne' with ⟨c₀, hc₀, hc₀r⟩
        exact ⟨c₀, .inl hc₀, by simp, hc₀r⟩
    · obtain ⟨i₀, hi₀I, hc_max⟩ : ∃ i₀ ∈ I, IsMaxOn (‖c ·‖ₑ) I i₀ :=
        exists_max_image _ (‖c ·‖ₑ) hI hIne
      by_cases! H : c i₀ ≠ 0 ∨ I = univ
      · exact ⟨c i₀, H, fun i hi ↦ by simpa [enorm] using! hc_max hi, hcr _ hi₀I⟩
      · have hc0 (i : ι) (hi : i ∈ I) : c i = 0 := by simpa [H] using hc_max hi
        have heg0 (i : ι) (hi : i ∈ I) : x i = 0 :=
          zero_smul_set_subset (α := 𝕜) (U i) (hc0 i hi ▸ hc i hi)
        have : (𝓝[≠] (0 : 𝕜)).NeBot := (hI₀.resolve_left H.2).resolve_left (by simpa)
        rcases exists_enorm_lt 𝕜 hr₀.ne' with ⟨c₁, hc₁, hc₁r⟩
        refine ⟨c₁, .inl hc₁, fun i hi ↦ ?_, hc₁r⟩
        simp [hc0 i hi]
  refine egauge_lt_iff.2 ⟨c₀, ?_, hc₀r⟩
  rw [smul_set_pi₀' hc₀]
  intro i hi
  exact (hU i hi).smul_mono (hc₀I i hi) (hc i hi)

/-- The extended gauge of a point `x` in an indexed product with finite index type
with respect to a product of balanced sets `U i`,
is the supremum of the extended gauges of the components of `x`
with respect to the corresponding balanced set.
-/
/-
**egauge_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：egauge_univ_pi [Finite ι] {U : forall i, Set (E i)} (hU : forall i, Balanc
ed 𝕜 (U i)) (x : forall i, E i) : egauge 𝕜 (univ.pi U) x = ⨆ i, egauge 𝕜 (U i) (
x i)
参数：E i；hU : forall i, Balanced 𝕜 (U i)；x : forall i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `egauge_pi'`：egauge_pi' {I : Set ι} (hI : I.Finite) {U : forall i, Set (E
 i)} (hU : forall i in I, Balanced 𝕜 (U i)) (x : forall i, E i) (hI₀ : I = univ 
…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The extended gauge of a point `x` in an indexed product with finite index type
with respect to a product of balanced sets `U i`,
is the supremum of the extended gauges of the components of `x`
with respect to the corresponding balanced set.
-/
theorem egauge_univ_pi [Finite ι] {U : ∀ i, Set (E i)} (hU : ∀ i, Balanced 𝕜 (U i)) (x : ∀ i, E i) :
    egauge 𝕜 (univ.pi U) x = ⨆ i, egauge 𝕜 (U i) (x i) :=
  egauge_pi' finite_univ (fun i _ ↦ hU i) x (.inl rfl) |>.trans <| by simp

/-- The extended gauge of a point `x` in an indexed product
with respect to a product of finitely many balanced sets `U i`, `i ∈ I`,
(and the whole spaces for the other indices)
is the supremum of the extended gauges of the components of `x`
with respect to the corresponding balanced set.

This version assumes that `𝕜` is a nontrivially normed division ring.
See also `egauge_univ_pi` for when `s = univ`,
and `egauge_pi'` for a version with more choices of the technical assumptions.
-/
/-
**egauge_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：egauge_pi [(𝓝[!=] (0 : 𝕜)).NeBot] {I : Set ι} {U : forall i, Set (E i)} (h
I : I.Finite) (hU : forall i in I, Balanced 𝕜 (U i)) (x : forall i, E i) : egaug
e 𝕜 (I.pi U) x = ⨆ i in I, egauge 𝕜 (U i) (x i)
参数：𝓝[!=] (0 : 𝕜)；E i；hI : I.Finite；hU : forall i in I, Balanced 𝕜 (U i)；x : fora
ll i, E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `egauge_pi'`：egauge_pi' {I : Set ι} (hI : I.Finite) {U : forall i, Set (E
 i)} (hU : forall i in I, Balanced 𝕜 (U i)) (x : forall i, E i) (hI₀ : I = univ 
…

--- 原说明 ---
The extended gauge of a point `x` in an indexed product
with respect to a product of finitely many balanced sets `U i`, `i ∈ I`,
(and the whole spaces for the other indices)
is the supremum of the extended gauges of the components of `x`
with respect to the corresponding balanced set.

This version assumes that `𝕜` is a nontrivially normed division ring.
See also `egauge_univ_pi` for when `s = univ`,
and `egauge_pi'` for a version with more choices of the technical assumptions.
-/
theorem egauge_pi [(𝓝[≠] (0 : 𝕜)).NeBot] {I : Set ι} {U : ∀ i, Set (E i)}
    (hI : I.Finite) (hU : ∀ i ∈ I, Balanced 𝕜 (U i)) (x : ∀ i, E i) :
    egauge 𝕜 (I.pi U) x = ⨆ i ∈ I, egauge 𝕜 (U i) (x i) :=
  egauge_pi' hI hU x <| .inr <| .inr inferInstance

end Pi

section SeminormedAddCommGroup

variable (𝕜 : Type*) [NormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
**div_le_egauge_closedBall** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_le_egauge_closedBall (r : Real>=0) (x : E) : ‖x‖ₑ / r <= egauge 𝕜 (clo
sedBall 0 r) x
参数：r : Real>=0；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_egauge_iff`：le_egauge_iff : r <= egauge 𝕜 s x ↔ forall c : 𝕜, x in c 
• s -> r <= ‖c‖ₑ
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `ENNReal.div_le_of_le_mul`：div_le_of_le_mul (h : a <= b * c) : a / c <= b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `enorm_le_coe`：∀ {E : Type u_8} [inst : NNNorm E] {x : E} {r : NNReal}, ‖
x‖ₑ ≤ ↑r ↔ ‖x‖₊ ≤ r
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
-/
lemma div_le_egauge_closedBall (r : ℝ≥0) (x : E) : ‖x‖ₑ / r ≤ egauge 𝕜 (closedBall 0 r) x := by
  rw [le_egauge_iff]
  rintro c ⟨y, hy, rfl⟩
  rw [mem_closedBall_zero_iff, ← coe_nnnorm, NNReal.coe_le_coe] at hy
  rw [enorm_smul]
  apply ENNReal.div_le_of_le_mul
  gcongr
  rwa [enorm_le_coe]
/-
**le_egauge_closedBall_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_egauge_closedBall_one (x : E) : ‖x‖ₑ <= egauge 𝕜 (closedBall 0 1) x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `div_le_egauge_closedBall`：div_le_egauge_closedBall (r : Real>=0) (x : E)
 : ‖x‖ₑ / r <= egauge 𝕜 (closedBall 0 r) x
-/
lemma le_egauge_closedBall_one (x : E) : ‖x‖ₑ ≤ egauge 𝕜 (closedBall 0 1) x := by
  simpa using div_le_egauge_closedBall 𝕜 1 x
/-
**div_le_egauge_ball** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_le_egauge_ball (r : Real>=0) (x : E) : ‖x‖ₑ / r <= egauge 𝕜 (ball 0 r)
 x
参数：r : Real>=0；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `div_le_egauge_closedBall`：div_le_egauge_closedBall (r : Real>=0) (x : E)
 : ‖x‖ₑ / r <= egauge 𝕜 (closedBall 0 r) x
· 使用引理 `egauge_anti`：egauge_anti (h : s subseteq t) (x : E) : egauge 𝕜 t x <= eg
auge 𝕜 s x
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
-/
lemma div_le_egauge_ball (r : ℝ≥0) (x : E) : ‖x‖ₑ / r ≤ egauge 𝕜 (ball 0 r) x :=
  (div_le_egauge_closedBall 𝕜 r x).trans <| egauge_anti _ ball_subset_closedBall _
/-
**le_egauge_ball_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_egauge_ball_one (x : E) : ‖x‖ₑ <= egauge 𝕜 (ball 0 1) x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `div_le_egauge_ball`：div_le_egauge_ball (r : Real>=0) (x : E) : ‖x‖ₑ / r 
<= egauge 𝕜 (ball 0 r) x
-/
lemma le_egauge_ball_one (x : E) : ‖x‖ₑ ≤ egauge 𝕜 (ball 0 1) x := by
  simpa using div_le_egauge_ball 𝕜 1 x

variable {𝕜}
variable {c : 𝕜} {x : E} {r : ℝ≥0}
/-
**egauge_ball_le_of_one_lt_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_ball_le_of_one_lt_norm (hc : 1 < ‖c‖) (h₀ : r != 0 ∨ ‖x‖ != 0) : eg
auge 𝕜 (ball 0 r) x <= ‖c‖ₑ * ‖x‖ₑ / r
参数：hc : 1 < ‖c‖；h₀ : r != 0 ∨ ‖x‖ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `ENNReal.div_zero`：div_zero (h : a != 0) : a / 0 = ∞
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.frequently_iff_neBot`：frequently_iff_neBot {l : Filter α} {p : α 
-> Prop} : (existsᶠ x in l, p x) ↔ NeBot (l ⊓ 𝓟 {x | p x})
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
（共 42 条，此处仅展示前 30 条）
-/
lemma egauge_ball_le_of_one_lt_norm (hc : 1 < ‖c‖) (h₀ : r ≠ 0 ∨ ‖x‖ ≠ 0) :
    egauge 𝕜 (ball 0 r) x ≤ ‖c‖ₑ * ‖x‖ₑ / r := by
  let : NontriviallyNormedField 𝕜 := ⟨c, hc⟩
  rcases eq_zero_or_pos r with rfl | hr
  · rw [ENNReal.coe_zero, ENNReal.div_zero (mul_ne_zero _ _)]
    · apply le_top
    · simpa using one_pos.trans hc
    · simpa [enorm, ← NNReal.coe_eq_zero] using h₀
  · rcases eq_or_ne ‖x‖ 0 with hx | hx
    · have hx' : ‖x‖ₑ = 0 := by simpa [enorm, ← coe_nnnorm, NNReal.coe_eq_zero] using hx
      simp only [hx', mul_zero, ENNReal.zero_div, nonpos_iff_eq_zero, egauge_eq_zero_iff]
      refine (frequently_iff_neBot.2 (inferInstance : NeBot (𝓝[≠] (0 : 𝕜)))).mono fun c hc ↦ ?_
      simp [mem_smul_set_iff_inv_smul_mem₀ hc, norm_smul, hx, hr]
    · rcases rescale_to_shell_semi_normed hc hr hx with ⟨a, ha₀, har, -, hainv⟩
      calc
        egauge 𝕜 (ball 0 r) x ≤ ↑(‖a‖₊⁻¹) :=
          egauge_le_of_smul_mem_of_ne (mem_ball_zero_iff.2 har) ha₀
        _ ≤ ↑(‖c‖₊ * ‖x‖₊ / r) := by rwa [ENNReal.coe_le_coe, div_eq_inv_mul, ← mul_assoc]
        _ ≤ ‖c‖ₑ * ‖x‖ₑ / r := ENNReal.coe_div_le.trans <| by simp [ENNReal.coe_mul, enorm]
/-
**egauge_ball_one_le_of_one_lt_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：egauge_ball_one_le_of_one_lt_norm (hc : 1 < ‖c‖) (x : E) : egauge 𝕜 (ball 
0 1) x <= ‖c‖ₑ * ‖x‖ₑ
参数：hc : 1 < ‖c‖；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `egauge_ball_le_of_one_lt_norm`：egauge_ball_le_of_one_lt_norm (hc : 1 < ‖
c‖) (h₀ : r != 0 ∨ ‖x‖ != 0) : egauge 𝕜 (ball 0 r) x <= ‖c‖ₑ * ‖x‖ₑ / r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma egauge_ball_one_le_of_one_lt_norm (hc : 1 < ‖c‖) (x : E) :
    egauge 𝕜 (ball 0 1) x ≤ ‖c‖ₑ * ‖x‖ₑ := by
  simpa using egauge_ball_le_of_one_lt_norm hc (.inl one_ne_zero)

end SeminormedAddCommGroup

