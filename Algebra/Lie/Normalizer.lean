/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.IdealOperations
public import Mathlib.Algebra.Lie.Quotient

/-!
# The normalizer of Lie submodules and subalgebras.

Given a Lie module `M` over a Lie subalgebra `L`, the normalizer of a Lie submodule `N ⊆ M` is
the Lie submodule with underlying set `{ m | ∀ (x : L), ⁅x, m⁆ ∈ N }`.

The lattice of Lie submodules thus has two natural operations, the normalizer: `N ↦ N.normalizer`
and the ideal operation: `N ↦ ⁅⊤, N⁆`; these are adjoint, i.e., they form a Galois connection. This
adjointness is the reason that we may define nilpotency in terms of either the upper or lower
central series.

Given a Lie subalgebra `H ⊆ L`, we may regard `H` as a Lie submodule of `L` over `H`, and thus
consider the normalizer. This turns out to be a Lie subalgebra.

## Main definitions

  * `LieSubmodule.normalizer`
  * `LieSubalgebra.normalizer`
  * `LieSubmodule.gc_top_lie_normalizer`

## Tags

lie algebra, normalizer
-/

@[expose] public section


variable {R L M M' : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

namespace LieSubmodule

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

/-- The normalizer of a Lie submodule.

See also `LieSubmodule.idealizer`. -/
/-
**LieSubmodule.normalizer** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：normalizer : LieSubmodule R L M where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalizer of a Lie submodule.

See also `LieSubmodule.idealizer`.
-/
def normalizer : LieSubmodule R L M where
  carrier := {m | ∀ x : L, ⁅x, m⁆ ∈ N}
  add_mem' hm₁ hm₂ x := by rw [lie_add]; exact N.add_mem' (hm₁ x) (hm₂ x)
  zero_mem' x := by simp
  smul_mem' t m hm x := by rw [lie_smul]; exact N.smul_mem' t (hm x)
  lie_mem {x m} hm y := by rw [leibniz_lie]; exact N.add_mem' (hm ⁅y, x⁆) (N.lie_mem (hm y))

@[simp]
/-
**LieSubmodule.mem_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_normalizer (m : M) : m in N.normalizer ↔ forall x : L, ⁅x, m⁆ in N
参数：m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_normalizer (m : M) : m ∈ N.normalizer ↔ ∀ x : L, ⁅x, m⁆ ∈ N :=
  Iff.rfl

@[simp]
/-
**LieSubmodule.le_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：le_normalizer : N <= N.normalizer
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.mem_normalizer`：mem_normalizer (m : M) : m in N.normalizer 
↔ forall x : L, ⁅x, m⁆ in N
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
-/
theorem le_normalizer : N ≤ N.normalizer := by
  intro m hm
  rw [mem_normalizer]
  exact fun x => N.lie_mem hm
/-
**LieSubmodule.normalizer_inf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：normalizer_inf : (N₁ ⊓ N₂).normalizer = N₁.normalizer ⊓ N₂.normalizer
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem normalizer_inf : (N₁ ⊓ N₂).normalizer = N₁.normalizer ⊓ N₂.normalizer := by
  ext; simp [← forall_and]

@[gcongr, mono]
/-
**LieSubmodule.normalizer_mono** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：normalizer_mono (h : N₁ <= N₂) : normalizer N₁ <= normalizer N₂
参数：h : N₁ <= N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.mem_normalizer`：mem_normalizer (m : M) : m in N.normalizer 
↔ forall x : L, ⁅x, m⁆ in N
-/
theorem normalizer_mono (h : N₁ ≤ N₂) : normalizer N₁ ≤ normalizer N₂ := by
  intro m hm
  rw [mem_normalizer] at hm ⊢
  exact fun x ↦ h (hm x)
/-
**LieSubmodule.monotone_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：monotone_normalizer : Monotone (normalizer : LieSubmodule R L M -> LieSubm
odule R L M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.normalizer_mono`：normalizer_mono (h : N₁ <= N₂) : normalize
r N₁ <= normalizer N₂
-/
theorem monotone_normalizer : Monotone (normalizer : LieSubmodule R L M → LieSubmodule R L M) :=
  fun _ _ ↦ normalizer_mono

@[simp]
/-
**LieSubmodule.comap_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：comap_normalizer (f : M' ->ₗ⁅R,L⁆ M) : N.normalizer.comap f = (N.comap f).
normalizer
参数：f : M' ->ₗ⁅R,L⁆ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LieModuleHom.map_lie`：map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x,
 m⁆ = ⁅x, f m⁆
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_normalizer (f : M' →ₗ⁅R,L⁆ M) : N.normalizer.comap f = (N.comap f).normalizer := by
  ext; simp
/-
**LieSubmodule.top_lie_le_iff_le_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmod
ule`。
形式化陈述：top_lie_le_iff_le_normalizer (N' : LieSubmodule R L M) : ⁅(⊤ : LieIdeal R 
L), N⁆ <= N' ↔ N <= N'.normalizer
参数：N' : LieSubmodule R L M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lie_le_iff`：lie_le_iff : ⁅I, N⁆ <= N' ↔ forall x in I, fora
ll m in N, ⁅x, m⁆ in N'
· 使用定理 `trivial`：True
-/
theorem top_lie_le_iff_le_normalizer (N' : LieSubmodule R L M) :
    ⁅(⊤ : LieIdeal R L), N⁆ ≤ N' ↔ N ≤ N'.normalizer := by rw [lie_le_iff]; tauto
/-
**LieSubmodule.gc_top_lie_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：gc_top_lie_normalizer : GaloisConnection (fun N : LieSubmodule R L M => ⁅(
⊤ : LieIdeal R L), N⁆) normalizer
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.top_lie_le_iff_le_normalizer`：top_lie_le_iff_le_normalizer 
(N' : LieSubmodule R L M) : ⁅(⊤ : LieIdeal R L), N⁆ <= N' ↔ N <= N'.normalizer
-/
theorem gc_top_lie_normalizer :
    GaloisConnection (fun N : LieSubmodule R L M => ⁅(⊤ : LieIdeal R L), N⁆) normalizer :=
  top_lie_le_iff_le_normalizer

variable (R L M) in
/-
**LieSubmodule.normalizer_bot_eq_maxTrivSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Submodule`。
形式化陈述：normalizer_bot_eq_maxTrivSubmodule : (⊥ : LieSubmodule R L M).normalizer =
 LieModule.maxTrivSubmodule R L M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normalizer_bot_eq_maxTrivSubmodule :
    (⊥ : LieSubmodule R L M).normalizer = LieModule.maxTrivSubmodule R L M :=
  rfl

/-- The idealizer of a Lie submodule.

See also `LieSubmodule.normalizer`. -/
/-
**LieSubmodule.idealizer** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：idealizer : LieIdeal R L where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The idealizer of a Lie submodule.

See also `LieSubmodule.normalizer`.
-/
def idealizer : LieIdeal R L where
  carrier := {x : L | ∀ m : M, ⁅x, m⁆ ∈ N}
  add_mem' := fun {x} {y} hx hy m ↦ by rw [add_lie]; exact N.add_mem (hx m) (hy m)
  zero_mem' := by simp
  smul_mem' := fun t {x} hx m ↦ by rw [smul_lie]; exact N.smul_mem t (hx m)
  lie_mem := fun {x} {y} hy m ↦ by rw [lie_lie]; exact sub_mem (N.lie_mem (hy m)) (hy ⁅x, m⁆)

@[simp]
/-
**LieSubmodule.mem_idealizer** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_idealizer {x : L} : x in N.idealizer ↔ forall m : M, ⁅x, m⁆ in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_idealizer {x : L} : x ∈ N.idealizer ↔ ∀ m : M, ⁅x, m⁆ ∈ N := Iff.rfl

@[simp]
/-
**LieSubmodule._root_.LieIdeal.idealizer_eq_normalizer** 是 Mathlib 中的一个引理，位于命名空间
 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LieIdeal.idealizer_eq_normalizer (I : LieIdeal R L) :
    I.idealizer = I.normalizer := by
  ext x; exact forall_congr' fun y ↦ by simp only [← lie_skew x y, neg_mem_iff]

end LieSubmodule

namespace LieSubalgebra

variable (H : LieSubalgebra R L)

/-- Regarding a Lie subalgebra `H ⊆ L` as a module over itself, its normalizer is in fact a Lie
subalgebra. -/
/-
**LieSubalgebra.normalizer** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：normalizer : LieSubalgebra R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Regarding a Lie subalgebra `H ⊆ L` as a module over itself, its normalizer is in
 fact a Lie
subalgebra.
-/
def normalizer : LieSubalgebra R L :=
  { H.toLieSubmodule.normalizer with
    lie_mem' := fun {y z} hy hz x => by
      rw [coe_bracket_of_module, mem_toLieSubmodule, leibniz_lie, ← lie_skew y, ← sub_eq_add_neg]
      exact H.sub_mem (hz ⟨_, hy x⟩) (hy ⟨_, hz x⟩) }
/-
**LieSubalgebra.mem_normalizer_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_normalizer_iff' (x : L) : x in H.normalizer ↔ forall y : L, y in H -> 
⁅y, x⁆ in H
参数：x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_normalizer_iff' (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅y, x⁆ ∈ H := by
  rw [Subtype.forall']; rfl
/-
**LieSubalgebra.mem_normalizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_normalizer_iff (x : L) : x in H.normalizer ↔ forall y : L, y in H -> ⁅
x, y⁆ in H
参数：x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.mem_normalizer_iff'`：mem_normalizer_iff' (x : L) : x in H.
normalizer ↔ forall y : L, y in H -> ⁅y, x⁆ in H
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_normalizer_iff (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅x, y⁆ ∈ H := by
  rw [mem_normalizer_iff']
  refine forall₂_congr fun y hy => ?_
  rw [← lie_skew, neg_mem_iff (G := L)]
/-
**LieSubalgebra.le_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：le_normalizer : H <= H.normalizer
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.le_normalizer`：le_normalizer : N <= N.normalizer
-/
theorem le_normalizer : H ≤ H.normalizer :=
  H.toLieSubmodule.le_normalizer
/-
**LieSubalgebra.coe_normalizer_eq_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSubal
gebra`。
形式化陈述：coe_normalizer_eq_normalizer : (H.toLieSubmodule.normalizer : Submodule R 
L) = H.normalizer
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_normalizer_eq_normalizer :
    (H.toLieSubmodule.normalizer : Submodule R L) = H.normalizer :=
  rfl

variable {H}
/-
**LieSubalgebra.lie_mem_sup_of_mem_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSuba
lgebra`。
形式化陈述：lie_mem_sup_of_mem_normalizer {x y z : L} (hx : x in H.normalizer) (hy : y
 in R ∙ x ⊔ ↑H) (hz : z in R ∙ x ⊔ ↑H) : ⁅y, z⁆ in R ∙ x ⊔ ↑H
参数：hx : x in H.normalizer；hy : y in R ∙ x ⊔ ↑H；hz : z in R ∙ x ⊔ ↑H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `lie_self`：lie_self : ⁅x, x⁆ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LieSubalgebra.add_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] [
inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   {x y : 
L}, x ∈ L' …
· 使用定理 `LieSubalgebra.smul_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   (t : R
) {x : L}, x…
· 使用定理 `LieSubalgebra.mem_normalizer_iff'`：mem_normalizer_iff' (x : L) : x in H.
normalizer ↔ forall y : L, y in H -> ⁅y, x⁆ in H
· 使用定理 `LieSubalgebra.mem_normalizer_iff`：mem_normalizer_iff (x : L) : x in H.no
rmalizer ↔ forall y : L, y in H -> ⁅x, y⁆ in H
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
-/
theorem lie_mem_sup_of_mem_normalizer {x y z : L} (hx : x ∈ H.normalizer) (hy : y ∈ R ∙ x ⊔ ↑H)
    (hz : z ∈ R ∙ x ⊔ ↑H) : ⁅y, z⁆ ∈ R ∙ x ⊔ ↑H := by
  rw [Submodule.mem_sup] at hy hz
  obtain ⟨u₁, hu₁, v, hv : v ∈ H, rfl⟩ := hy
  obtain ⟨u₂, hu₂, w, hw : w ∈ H, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu₂
  apply Submodule.mem_sup_right
  simp only [LieSubalgebra.mem_toSubmodule, smul_lie, add_lie, zero_add, lie_add, smul_zero,
    lie_smul, lie_self]
  refine H.add_mem (H.smul_mem s ?_) (H.add_mem (H.smul_mem t ?_) (H.lie_mem hv hw))
  exacts [(H.mem_normalizer_iff' x).mp hx v hv, (H.mem_normalizer_iff x).mp hx w hw]

/-- A Lie subalgebra is an ideal of its normalizer. -/
/-
**LieSubalgebra.ideal_in_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：ideal_in_normalizer {x y : L} (hx : x in H.normalizer) (hy : y in H) : ⁅x,
 y⁆ in H
参数：hx : x in H.normalizer；hy : y in H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L

--- 原说明 ---
A Lie subalgebra is an ideal of its normalizer.
-/
theorem ideal_in_normalizer {x y : L} (hx : x ∈ H.normalizer) (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [← lie_skew, neg_mem_iff (G := L)]
  exact hx ⟨y, hy⟩

/-- A Lie subalgebra `H` is an ideal of any Lie subalgebra `K` containing `H` and contained in the
normalizer of `H`. -/
/-
**LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer** 是 Mathlib 中的一个定理，位于命名空间
 `LieSubalgebra`。
形式化陈述：exists_nested_lieIdeal_ofLe_normalizer {K : LieSubalgebra R L} (h₁ : H <= 
K) (h₂ : K <= H.normalizer) : exists I : LieIdeal R K, (I : LieSubalgebra R K) =
 ofLe h₁
参数：h₁ : H <= K；h₂ : K <= H.normalizer。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.exists_nested_lieIdeal_coe_eq_iff`：exists_nested_lieIdeal_
coe_eq_iff {K' : LieSubalgebra R L} (h : K <= K') : (exists I : LieIdeal R K', ↑
I = ofLe h) ↔ forall x y : L, x in K'…
· 使用定理 `LieSubalgebra.ideal_in_normalizer`：ideal_in_normalizer {x y : L} (hx : x
 in H.normalizer) (hy : y in H) : ⁅x, y⁆ in H

--- 原说明 ---
A Lie subalgebra `H` is an ideal of any Lie subalgebra `K` containing `H` and co
ntained in the
normalizer of `H`.
-/
theorem exists_nested_lieIdeal_ofLe_normalizer {K : LieSubalgebra R L} (h₁ : H ≤ K)
    (h₂ : K ≤ H.normalizer) : ∃ I : LieIdeal R K, (I : LieSubalgebra R K) = ofLe h₁ := by
  rw [exists_nested_lieIdeal_coe_eq_iff]
  exact fun x y hx hy => ideal_in_normalizer (h₂ hx) hy

variable (H)
/-
**LieSubalgebra.normalizer_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`
。
形式化陈述：normalizer_eq_self_iff : H.normalizer = H ↔ (LieModule.maxTrivSubmodule R 
H <| L ⧸ H.toLieSubmodule) = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.eq_bot_iff`：∀ {R : Type u} {L : Type v} {M : Type w} [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.
Module R M] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.mem_normalizer_iff'`：mem_normalizer_iff' (x : L) : x in H.
normalizer ↔ forall y : L, y in H -> ⁅y, x⁆ in H
· 使用定理 `LieSubmodule.Quotient.mk_eq_zero`：mk_eq_zero {m : M} : mk' N m = 0 ↔ m i
n N
· 使用定理 `LieModuleHom.map_lie`：map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x,
 m⁆ = ⁅x, f m⁆
· 使用定理 `Submodule.Quotient.quot_mk_eq_mk`：quot_mk_eq_mk {p : Submodule R M} (x :
 M) : (Quot.mk _ x : M ⧸ p) = mk x
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `LieSubalgebra.coe_toLieSubmodule`：coe_toLieSubmodule : (K.toLieSubmodule
 : Submodule R L) = K
· 使用定理 `LieSubalgebra.mem_toSubmodule`：mem_toSubmodule {x : L} : x in (L' : Subm
odule R L) ↔ x in L'
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubalgebra.coe_bracket_of_module`：coe_bracket_of_module (x : L') (m :
 M) : ⁅x, m⁆ = ⁅(x : L), m⁆
· 使用定理 `Submodule.coe_mk`：coe_mk (x : M) (hx : x in p) : ((⟨x, hx⟩ : p) : M) = x
· 使用定理 `LieSubalgebra.mem_toLieSubmodule`：mem_toLieSubmodule (x : L) : x in K.to
LieSubmodule ↔ x in K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieSubmodule.Quotient.mk'_apply`：∀ {R : Type u} {L : Type v} {M : Type w
} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 :
 _root_.Module R M] […
· 使用定理 `LieSubalgebra.le_normalizer`：le_normalizer : H <= H.normalizer
-/
theorem normalizer_eq_self_iff :
    H.normalizer = H ↔ (LieModule.maxTrivSubmodule R H <| L ⧸ H.toLieSubmodule) = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  refine ⟨fun h => ?_, fun h => le_antisymm ?_ H.le_normalizer⟩
  · rintro ⟨x⟩ hx
    suffices x ∈ H by rwa [Submodule.Quotient.quot_mk_eq_mk, Submodule.Quotient.mk_eq_zero,
      coe_toLieSubmodule, mem_toSubmodule]
    rw [← h, H.mem_normalizer_iff']
    intro y hy
    replace hx : ⁅_, LieSubmodule.Quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩
    rwa [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero] at hx
  · intro x hx
    let y := LieSubmodule.Quotient.mk' H.toLieSubmodule x
    have hy : y ∈ LieModule.maxTrivSubmodule R H (L ⧸ H.toLieSubmodule) := by
      rintro ⟨z, hz⟩
      rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero, coe_bracket_of_module,
        Submodule.coe_mk, mem_toLieSubmodule]
      exact (H.mem_normalizer_iff' x).mp hx z hz
    simpa [y] using h y hy

end LieSubalgebra

