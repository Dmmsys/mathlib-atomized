/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.Group.Subgroup
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Normed groups homomorphisms

This file gathers definitions and elementary constructions about bounded group homomorphisms
between normed (abelian) groups (abbreviated to "normed group homs").

The main lemmas relate the boundedness condition to continuity and Lipschitzness.

The main construction is to endow the type of normed group homs between two given normed groups
with a group structure and a norm, giving rise to a normed group structure. We provide several
simple constructions for normed group homs, like kernel, range and equalizer.

Some easy other constructions are related to subgroups of normed groups.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory of `SeminormedAddGroupHom` and we specialize to `NormedAddGroupHom` when needed.
-/

@[expose] public section


noncomputable section

open NNReal

-- TODO: migrate to the new morphism / morphism_class style
/-- A morphism of seminormed abelian groups is a bounded group homomorphism. -/
/-
**NormedAddGroupHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(V : Type u_1) → (W : Type u_2) → [SeminormedAddCommGroup V] → [Seminormed
AddCommGroup W] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of seminormed abelian groups is a bounded group homomorphism.
-/
structure NormedAddGroupHom (V W : Type*) [SeminormedAddCommGroup V]
  [SeminormedAddCommGroup W] where
  /-- The function underlying a `NormedAddGroupHom` -/
  toFun : V → W
  /-- A `NormedAddGroupHom` is additive. -/
  map_add' : ∀ v₁ v₂, toFun (v₁ + v₂) = toFun v₁ + toFun v₂
  /-- A `NormedAddGroupHom` is bounded. -/
  bound' : ∃ C, ∀ v, ‖toFun v‖ ≤ C * ‖v‖

namespace AddMonoidHom

variable {V W : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
  {f g : NormedAddGroupHom V W}

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `AddMonoidHom.mkNormedAddGroupHom'` for a version that uses `ℝ≥0` for the bound. -/
/-
**AddMonoidHom.mkNormedAddGroupHom** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mkNormedAddGroupHom (f : V ->+ W) (C : Real) (h : forall v, ‖f v‖ <= C * ‖
v‖) : NormedAddGroupHom V W
参数：f : V ->+ W；C : Real；h : forall v, ‖f v‖ <= C * ‖v‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associate to a group homomorphism a bounded group homomorphism under a norm cont
rol condition.

See `AddMonoidHom.mkNormedAddGroupHom'` for a version that uses `ℝ≥0` for the bo
und.
-/
def mkNormedAddGroupHom (f : V →+ W) (C : ℝ) (h : ∀ v, ‖f v‖ ≤ C * ‖v‖) : NormedAddGroupHom V W :=
  { f with bound' := ⟨C, h⟩ }

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `AddMonoidHom.mkNormedAddGroupHom` for a version that uses `ℝ` for the bound. -/
/-
**AddMonoidHom.mkNormedAddGroupHom'** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mkNormedAddGroupHom' (f : V ->+ W) (C : Real>=0) (hC : forall x, ‖f x‖₊ <=
 C * ‖x‖₊) : NormedAddGroupHom V W
参数：f : V ->+ W；C : Real>=0；hC : forall x, ‖f x‖₊ <= C * ‖x‖₊。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associate to a group homomorphism a bounded group homomorphism under a norm cont
rol condition.

See `AddMonoidHom.mkNormedAddGroupHom` for a version that uses `ℝ` for the bound
.
-/
def mkNormedAddGroupHom' (f : V →+ W) (C : ℝ≥0) (hC : ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊) :
    NormedAddGroupHom V W :=
  { f with bound' := ⟨C, hC⟩ }

end AddMonoidHom

/-
**exists_pos_bound_of_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pos_bound_of_bound {V W : Type*} [SeminormedAddCommGroup V] [Semino
rmedAddCommGroup W] {f : V -> W} (M : Real) (h : forall x, ‖f x‖ <= M * ‖x‖) : e
xists N, 0 < N ∧ forall x, ‖f x‖ <= N * ‖x‖
参数：M : Real；h : forall x, ‖f x‖ <= M * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem exists_pos_bound_of_bound {V W : Type*} [SeminormedAddCommGroup V]
    [SeminormedAddCommGroup W] {f : V → W} (M : ℝ) (h : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    ∃ N, 0 < N ∧ ∀ x, ‖f x‖ ≤ N * ‖x‖ :=
  ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x =>
    calc
      ‖f x‖ ≤ M * ‖x‖ := h x
      _ ≤ max M 1 * ‖x‖ := by gcongr; apply le_max_left
      ⟩

namespace NormedAddGroupHom

variable {V V₁ V₂ V₃ : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup V₁]
  [SeminormedAddCommGroup V₂] [SeminormedAddCommGroup V₃]

variable {f g : NormedAddGroupHom V₁ V₂}

/-- A Lipschitz continuous additive homomorphism is a normed additive group homomorphism. -/
/-
**NormedAddGroupHom.ofLipschitz** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：ofLipschitz (f : V₁ ->+ V₂) {K : Real>=0} (h : LipschitzWith K f) : Normed
AddGroupHom V₁ V₂
参数：f : V₁ ->+ V₂；h : LipschitzWith K f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lipschitz continuous additive homomorphism is a normed additive group homomorp
hism.
-/
def ofLipschitz (f : V₁ →+ V₂) {K : ℝ≥0} (h : LipschitzWith K f) : NormedAddGroupHom V₁ V₂ :=
  f.mkNormedAddGroupHom K fun x ↦ by simpa only [map_zero, dist_zero_right] using h.dist_le_mul x 0
/-
**NormedAddGroupHom.funLike** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：funLike : FunLike (NormedAddGroupHom V₁ V₂) V₁ V₂ where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr
/-
**NormedAddGroupHom.toAddMonoidHomClass** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGrou
pHom`。
形式化陈述：toAddMonoidHomClass : AddMonoidHomClass (NormedAddGroupHom V₁ V₂) V₁ V₂ wh
ere map_add f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.map_add'`：∀ {V : Type u_1} {W : Type u_2} [inst : Semi
normedAddCommGroup V] [inst_1 : SeminormedAddCommGroup W]   (self : NormedAddGro
upHom V W) (v₁ v…
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
-/
instance toAddMonoidHomClass : AddMonoidHomClass (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  map_add f := f.map_add'
  map_zero f := (AddMonoidHom.mk' f.toFun f.map_add').map_zero

initialize_simps_projections NormedAddGroupHom (toFun → apply)
/-
**NormedAddGroupHom.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_inj (H : (f : V₁ -> V₂) = g) : f = g
参数：H : (f : V₁ -> V₂) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_inj (H : (f : V₁ → V₂) = g) : f = g := by
  cases f; cases g; congr
/-
**NormedAddGroupHom.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_injective : @Function.Injective (NormedAddGroupHom V₁ V₂) (V₁ -> V₂) t
oFun
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.coe_inj`：coe_inj (H : (f : V₁ -> V₂) = g) : f = g
-/
theorem coe_injective : @Function.Injective (NormedAddGroupHom V₁ V₂) (V₁ → V₂) toFun := by
  apply coe_inj
/-
**NormedAddGroupHom.coe_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_inj_iff : f = g ↔ (f : V₁ -> V₂) = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.coe_inj`：coe_inj (H : (f : V₁ -> V₂) = g) : f = g
-/
theorem coe_inj_iff : f = g ↔ (f : V₁ → V₂) = g :=
  ⟨congr_arg _, coe_inj⟩

@[ext]
/-
**NormedAddGroupHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：ext (H : forall x, f x = g x) : f = g
参数：H : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.coe_inj`：coe_inj (H : (f : V₁ -> V₂) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext (H : ∀ x, f x = g x) : f = g :=
  coe_inj <| funext H

variable (f g)

@[simp]
/-
**NormedAddGroupHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：toFun_eq_coe : f.toFun = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe : f.toFun = f :=
  rfl
/-
**NormedAddGroupHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_mk (f) (h₁) (h₂) (h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : NormedAddGroupHom V₁ V₂) =
 f
参数：f；h₁；h₂；h₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f) (h₁) (h₂) (h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : NormedAddGroupHom V₁ V₂) = f :=
  rfl

@[simp]
/-
**NormedAddGroupHom.coe_mkNormedAddGroupHom** 是 Mathlib 中的一个定理，位于命名空间 `NormedAdd
GroupHom`。
形式化陈述：coe_mkNormedAddGroupHom (f : V₁ ->+ V₂) (C) (hC) : ⇑(f.mkNormedAddGroupHom
 C hC) = f
参数：f : V₁ ->+ V₂；C；hC。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mkNormedAddGroupHom (f : V₁ →+ V₂) (C) (hC) : ⇑(f.mkNormedAddGroupHom C hC) = f :=
  rfl

@[simp]
/-
**NormedAddGroupHom.coe_mkNormedAddGroupHom'** 是 Mathlib 中的一个定理，位于命名空间 `NormedAd
dGroupHom`。
形式化陈述：coe_mkNormedAddGroupHom' (f : V₁ ->+ V₂) (C) (hC) : ⇑(f.mkNormedAddGroupHo
m' C hC) = f
参数：f : V₁ ->+ V₂；C；hC。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mkNormedAddGroupHom' (f : V₁ →+ V₂) (C) (hC) : ⇑(f.mkNormedAddGroupHom' C hC) = f :=
  rfl

/-- The group homomorphism underlying a bounded group homomorphism. -/
/-
**NormedAddGroupHom.toAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`
。
形式化陈述：toAddMonoidHom (f : NormedAddGroupHom V₁ V₂) : V₁ ->+ V₂
参数：f : NormedAddGroupHom V₁ V₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.map_add'`：∀ {V : Type u_1} {W : Type u_2} [inst : Semi
normedAddCommGroup V] [inst_1 : SeminormedAddCommGroup W]   (self : NormedAddGro
upHom V W) (v₁ v…

--- 原说明 ---
The group homomorphism underlying a bounded group homomorphism.
-/
def toAddMonoidHom (f : NormedAddGroupHom V₁ V₂) : V₁ →+ V₂ :=
  AddMonoidHom.mk' f f.map_add'

@[simp]
/-
**NormedAddGroupHom.coe_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroup
Hom`。
形式化陈述：coe_toAddMonoidHom : ⇑f.toAddMonoidHom = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddMonoidHom : ⇑f.toAddMonoidHom = f :=
  rfl
/-
**NormedAddGroupHom.toAddMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `NormedAd
dGroupHom`。
形式化陈述：toAddMonoidHom_injective : Function.Injective (@NormedAddGroupHom.toAddMon
oidHom V₁ V₂ _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.coe_inj`：coe_inj (H : (f : V₁ -> V₂) = g) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedAddGroupHom.coe_toAddMonoidHom`：coe_toAddMonoidHom : ⇑f.toAddMonoi
dHom = f
-/
theorem toAddMonoidHom_injective :
    Function.Injective (@NormedAddGroupHom.toAddMonoidHom V₁ V₂ _ _) := fun f g h =>
  coe_inj <| by rw [← coe_toAddMonoidHom f, ← coe_toAddMonoidHom g, h]

@[simp]
/-
**NormedAddGroupHom.mk_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupH
om`。
形式化陈述：mk_toAddMonoidHom (f) (h₁) (h₂) : (⟨f, h₁, h₂⟩ : NormedAddGroupHom V₁ V₂).
toAddMonoidHom = AddMonoidHom.mk' f h₁
参数：f；h₁；h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_toAddMonoidHom (f) (h₁) (h₂) :
    (⟨f, h₁, h₂⟩ : NormedAddGroupHom V₁ V₂).toAddMonoidHom = AddMonoidHom.mk' f h₁ :=
  rfl
/-
**NormedAddGroupHom.bound** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：bound : exists C, 0 < C ∧ forall x, ‖f x‖ <= C * ‖x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.bound'`：∀ {V : Type u_1} {W : Type u_2} [inst : Semino
rmedAddCommGroup V] [inst_1 : SeminormedAddCommGroup W]   (self : NormedAddGroup
Hom V W), ∃ C,…
· 使用定理 `exists_pos_bound_of_bound`：exists_pos_bound_of_bound {V W : Type*} [Semi
normedAddCommGroup V] [SeminormedAddCommGroup W] {f : V -> W} (M : Real) (h : fo
rall x, ‖f x‖ <…
-/
theorem bound : ∃ C, 0 < C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖ :=
  let ⟨_C, hC⟩ := f.bound'
  exists_pos_bound_of_bound _ hC
/-
**NormedAddGroupHom.antilipschitz_of_norm_ge** 是 Mathlib 中的一个定理，位于命名空间 `NormedAd
dGroupHom`。
形式化陈述：antilipschitz_of_norm_ge {K : Real>=0} (h : forall x, ‖x‖ <= K * ‖f x‖) : 
AntilipschitzWith K f
参数：h : forall x, ‖x‖ <= K * ‖f x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
-/
theorem antilipschitz_of_norm_ge {K : ℝ≥0} (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist fun x y => by simpa only [dist_eq_norm, map_sub] using h (x - y)

/-- A normed group hom is surjective on the subgroup `K` with constant `C` if every element
`x` of `K` has a preimage whose norm is bounded above by `C*‖x‖`. This is a more
abstract version of `f` having a right inverse defined on `K` with operator norm
at most `C`. -/
/-
**NormedAddGroupHom.SurjectiveOnWith** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHo
m`。
形式化陈述：SurjectiveOnWith (f : NormedAddGroupHom V₁ V₂) (K : AddSubgroup V₂) (C : R
eal) : Prop
参数：f : NormedAddGroupHom V₁ V₂；K : AddSubgroup V₂；C : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed group hom is surjective on the subgroup `K` with constant `C` if every 
element
`x` of `K` has a preimage whose norm is bounded above by `C*‖x‖`. This is a more
abstract version of `f` having a right inverse defined on `K` with operator norm
at most `C`.
-/
def SurjectiveOnWith (f : NormedAddGroupHom V₁ V₂) (K : AddSubgroup V₂) (C : ℝ) : Prop :=
  ∀ h ∈ K, ∃ g, f g = h ∧ ‖g‖ ≤ C * ‖h‖
/-
**NormedAddGroupHom.SurjectiveOnWith.mono** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGr
oupHom.SurjectiveOnWith`。
形式化陈述：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : SeminormedAddCommGroup V₁] [inst
_1 : SeminormedAddCommGroup V₂]   {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup
 V₂} {C C' : ℝ},   f.SurjectiveOnWith K C → C ≤ C' → f.SurjectiveOnWith K C'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem SurjectiveOnWith.mono {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C C' : ℝ}
    (h : f.SurjectiveOnWith K C) (H : C ≤ C') : f.SurjectiveOnWith K C' := by
  intro k k_in
  rcases h k k_in with ⟨g, rfl, hg⟩
  use g, rfl
  by_cases Hg : ‖f g‖ = 0
  · simpa [Hg] using hg
  · exact hg.trans (by gcongr)
/-
**NormedAddGroupHom.SurjectiveOnWith.exists_pos** 是 Mathlib 中的一个定理，位于命名空间 `Norme
dAddGroupHom.SurjectiveOnWith`。
形式化陈述：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : SeminormedAddCommGroup V₁] [inst
_1 : SeminormedAddCommGroup V₂]   {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup
 V₂} {C : ℝ}, f.SurjectiveOnWith K C → ∃ C' > 0, f.SurjectiveOnWith K C'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 43 条，此处仅展示前 30 条）
-/
theorem SurjectiveOnWith.exists_pos {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : ℝ}
    (h : f.SurjectiveOnWith K C) : ∃ C' > 0, f.SurjectiveOnWith K C' := by
  refine ⟨|C| + 1, ?_, ?_⟩
  · linarith [abs_nonneg C]
  · apply h.mono
    linarith [le_abs_self C]
/-
**NormedAddGroupHom.SurjectiveOnWith.surjOn** 是 Mathlib 中的一个定理，位于命名空间 `NormedAdd
GroupHom.SurjectiveOnWith`。
形式化陈述：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : SeminormedAddCommGroup V₁] [inst
_1 : SeminormedAddCommGroup V₂]   {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup
 V₂} {C : ℝ}, f.SurjectiveOnWith K C → Set.SurjOn (⇑f) Set.univ ↑K
参数：⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem SurjectiveOnWith.surjOn {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : ℝ}
    (h : f.SurjectiveOnWith K C) : Set.SurjOn f Set.univ K := fun x hx =>
  (h x hx).imp fun _a ⟨ha, _⟩ => ⟨Set.mem_univ _, ha⟩

/-! ### The operator norm -/


/-- The operator norm of a seminormed group homomorphism is the inf of all its bounds. -/
/-
**NormedAddGroupHom.opNorm** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：opNorm (f : NormedAddGroupHom V₁ V₂)
参数：f : NormedAddGroupHom V₁ V₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The operator norm of a seminormed group homomorphism is the inf of all its bound
s.
-/
def opNorm (f : NormedAddGroupHom V₁ V₂) :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ }
/-
**NormedAddGroupHom.hasOpNorm** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：hasOpNorm : Norm (NormedAddGroupHom V₁ V₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasOpNorm : Norm (NormedAddGroupHom V₁ V₂) :=
  ⟨opNorm⟩
/-
**NormedAddGroupHom.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：norm_def : ‖f‖ = sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def : ‖f‖ = sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  rfl

-- So that invocations of `le_csInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
/-
**NormedAddGroupHom.bounds_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
`。
形式化陈述：bounds_nonempty {f : NormedAddGroupHom V₁ V₂} : exists c, c in { c | 0 <= 
c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.bound`：bound : exists C, 0 < C ∧ forall x, ‖f x‖ <= C 
* ‖x‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem bounds_nonempty {f : NormedAddGroupHom V₁ V₂} :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩
/-
**NormedAddGroupHom.bounds_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
`。
形式化陈述：bounds_bddBelow {f : NormedAddGroupHom V₁ V₂} : BddBelow { c | 0 <= c ∧ fo
rall x, ‖f x‖ <= c * ‖x‖ }
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bounds_bddBelow {f : NormedAddGroupHom V₁ V₂} :
    BddBelow { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩
/-
**NormedAddGroupHom.opNorm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：opNorm_nonneg : 0 <= ‖f‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `NormedAddGroupHom.bounds_nonempty`：bounds_nonempty {f : NormedAddGroupHo
m V₁ V₂} : exists c, c in { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
-/
theorem opNorm_nonneg : 0 ≤ ‖f‖ :=
  le_csInf bounds_nonempty fun _ ⟨hx, _⟩ => hx

/-- The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
/-
**NormedAddGroupHom.le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖
参数：x : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.bound`：bound : exists C, 0 < C ∧ forall x, ‖f x‖ <= C 
* ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `NormedAddGroupHom.bounds_nonempty`：bounds_nonempty {f : NormedAddGroupHo
m V₁ V₂} : exists c, c in { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`.
-/
theorem le_opNorm (x : V₁) : ‖f x‖ ≤ ‖f‖ * ‖x‖ := by
  obtain ⟨C, _Cpos, hC⟩ := f.bound
  replace hC := hC x
  by_cases h : ‖x‖ = 0
  · rwa [h, mul_zero] at hC ⊢
  have hlt : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
  exact
    (div_le_iff₀ hlt).mp
      (le_csInf bounds_nonempty fun c ⟨_, hc⟩ => (div_le_iff₀ hlt).mpr <| by apply hc)
/-
**NormedAddGroupHom.le_opNorm_of_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
`。
形式化陈述：le_opNorm_of_le {c : Real} {x} (h : ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c
参数：h : ‖x‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `NormedAddGroupHom.le_opNorm`：le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NormedAddGroupHom.opNorm_nonneg`：opNorm_nonneg : 0 <= ‖f‖
-/
theorem le_opNorm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
  le_trans (f.le_opNorm x) (by gcongr; exact f.opNorm_nonneg)
/-
**NormedAddGroupHom.le_of_opNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
`。
形式化陈述：le_of_opNorm_le {c : Real} (h : ‖f‖ <= c) (x : V₁) : ‖f x‖ <= c * ‖x‖
参数：h : ‖f‖ <= c；x : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `NormedAddGroupHom.le_opNorm`：le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem le_of_opNorm_le {c : ℝ} (h : ‖f‖ ≤ c) (x : V₁) : ‖f x‖ ≤ c * ‖x‖ :=
  (f.le_opNorm x).trans (by gcongr)

/-- continuous linear maps are Lipschitz continuous. -/
/-
**NormedAddGroupHom.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：lipschitz : LipschitzWith ⟨‖f‖, opNorm_nonneg f⟩ f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `NormedAddGroupHom.opNorm_nonneg`：opNorm_nonneg : 0 <= ‖f‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `NormedAddGroupHom.le_opNorm`：le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖

--- 原说明 ---
continuous linear maps are Lipschitz continuous.
-/
theorem lipschitz : LipschitzWith ⟨‖f‖, opNorm_nonneg f⟩ f :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    apply le_opNorm
/-
**NormedAddGroupHom.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupH
om`。
形式化陈述：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : SeminormedAddCommGroup V₁] [inst
_1 : SeminormedAddCommGroup V₂]   (f : NormedAddGroupHom V₁ V₂), UniformContinuo
us ⇑f
参数：f : NormedAddGroupHom V₁ V₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `NormedAddGroupHom.opNorm_nonneg`：opNorm_nonneg : 0 <= ‖f‖
· 使用定理 `NormedAddGroupHom.lipschitz`：lipschitz : LipschitzWith ⟨‖f‖, opNorm_nonn
eg f⟩ f
-/
protected theorem uniformContinuous (f : NormedAddGroupHom V₁ V₂) : UniformContinuous f :=
  f.lipschitz.uniformContinuous

@[continuity]
/-
**NormedAddGroupHom.continuous** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : SeminormedAddCommGroup V₁] [inst
_1 : SeminormedAddCommGroup V₂]   (f : NormedAddGroupHom V₁ V₂), Continuous ⇑f
参数：f : NormedAddGroupHom V₁ V₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `NormedAddGroupHom.uniformContinuous`：∀ {V₁ : Type u_2} {V₂ : Type u_3} [
inst : SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : No
rmedAddGroupHom V₁ V₂), U…
-/
protected theorem continuous (f : NormedAddGroupHom V₁ V₂) : Continuous f :=
  f.uniformContinuous.continuous
/-
**NormedAddGroupHom.** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMapClass (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  map_continuous := fun f => f.continuous
/-
**NormedAddGroupHom.ratio_le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
`。
形式化陈述：ratio_le_opNorm (x : V₁) : ‖f x‖ / ‖x‖ <= ‖f‖
参数：x : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_le_of_le_mul₀`：div_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a 
<= c * b) : a / b <= c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `NormedAddGroupHom.opNorm_nonneg`：opNorm_nonneg : 0 <= ‖f‖
· 使用定理 `NormedAddGroupHom.le_opNorm`：le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem ratio_le_opNorm (x : V₁) : ‖f x‖ / ‖x‖ ≤ ‖f‖ :=
  div_le_of_le_mul₀ (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
/-
**NormedAddGroupHom.opNorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
`。
形式化陈述：opNorm_le_bound {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖
) : ‖f‖ <= M
参数：hMp : 0 <= M；hM : forall x, ‖f x‖ <= M * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `NormedAddGroupHom.bounds_bddBelow`：bounds_bddBelow {f : NormedAddGroupHo
m V₁ V₂} : BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }

--- 原说明 ---
If one controls the norm of every `f x`, then one controls the norm of `f`.
-/
theorem opNorm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩
/-
**NormedAddGroupHom.opNorm_eq_of_bounds** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGrou
pHom`。
形式化陈述：opNorm_eq_of_bounds {M : Real} (M_nonneg : 0 <= M) (h_above : forall x, ‖f
 x‖ <= M * ‖x‖) (h_below : forall N >= 0, (forall x, ‖f x‖ <= N * ‖x‖) -> M <= N
) : ‖f‖ = M
参数：M_nonneg : 0 <= M；h_above : forall x, ‖f x‖ <= M * ‖x‖；h_below : forall N >= 
0, (forall x, ‖f x‖ <= N * ‖x‖) -> M <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_csInf_iff`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {
s : Set α} {a : α},   BddBelow s → s.Nonempty → (a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b)
· 使用定理 `NormedAddGroupHom.bounds_bddBelow`：bounds_bddBelow {f : NormedAddGroupHo
m V₁ V₂} : BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
-/
theorem opNorm_eq_of_bounds {M : ℝ} (M_nonneg : 0 ≤ M) (h_above : ∀ x, ‖f x‖ ≤ M * ‖x‖)
    (h_below : ∀ N ≥ 0, (∀ x, ‖f x‖ ≤ N * ‖x‖) → M ≤ N) : ‖f‖ = M :=
  le_antisymm (f.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff NormedAddGroupHom.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)
/-
**NormedAddGroupHom.opNorm_le_of_lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddG
roupHom`。
形式化陈述：opNorm_le_of_lipschitz {f : NormedAddGroupHom V₁ V₂} {K : Real>=0} (hf : L
ipschitzWith K f) : ‖f‖ <= K
参数：hf : LipschitzWith K f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
-/
theorem opNorm_le_of_lipschitz {f : NormedAddGroupHom V₁ V₂} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ‖f‖ ≤ K :=
  f.opNorm_le_bound K.2 fun x => by simpa only [dist_zero_right, map_zero] using hf.dist_le_mul x 0

/-- If a bounded group homomorphism map is constructed from a group homomorphism via the constructor
`AddMonoidHom.mkNormedAddGroupHom`, then its norm is bounded by the bound given to the constructor
if it is nonnegative. -/
/-
**NormedAddGroupHom.mkNormedAddGroupHom_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Norme
dAddGroupHom`。
形式化陈述：mkNormedAddGroupHom_norm_le (f : V₁ ->+ V₂) {C : Real} (hC : 0 <= C) (h : 
forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkNormedAddGroupHom C h‖ <= C
参数：f : V₁ ->+ V₂；hC : 0 <= C；h : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M

--- 原说明 ---
If a bounded group homomorphism map is constructed from a group homomorphism via
 the constructor
`AddMonoidHom.mkNormedAddGroupHom`, then its norm is bounded by the bound given 
to the constructor
if it is nonnegative.
-/
theorem mkNormedAddGroupHom_norm_le (f : V₁ →+ V₂) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkNormedAddGroupHom C h‖ ≤ C :=
  opNorm_le_bound _ hC h

/-- If a bounded group homomorphism map is constructed from a group homomorphism via the constructor
`NormedAddGroupHom.ofLipschitz`, then its norm is bounded by the bound given to the constructor. -/
/-
**NormedAddGroupHom.ofLipschitz_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGrou
pHom`。
形式化陈述：ofLipschitz_norm_le (f : V₁ ->+ V₂) {K : Real>=0} (h : LipschitzWith K f) 
: ‖ofLipschitz f h‖ <= K
参数：f : V₁ ->+ V₂；h : LipschitzWith K f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.mkNormedAddGroupHom_norm_le`：mkNormedAddGroupHom_norm_
le (f : V₁ ->+ V₂) {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖
f.mkNormedAddGroupHom C h‖ <= C
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r

--- 原说明 ---
If a bounded group homomorphism map is constructed from a group homomorphism via
 the constructor
`NormedAddGroupHom.ofLipschitz`, then its norm is bounded by the bound given to 
the constructor.
-/
theorem ofLipschitz_norm_le (f : V₁ →+ V₂) {K : ℝ≥0} (h : LipschitzWith K f) :
    ‖ofLipschitz f h‖ ≤ K :=
  mkNormedAddGroupHom_norm_le f K.coe_nonneg _

/-- If a bounded group homomorphism map is constructed from a group homomorphism
via the constructor `AddMonoidHom.mkNormedAddGroupHom`, then its norm is bounded by the bound
given to the constructor or zero if this bound is negative. -/
/-
**NormedAddGroupHom.mkNormedAddGroupHom_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 `Norm
edAddGroupHom`。
形式化陈述：mkNormedAddGroupHom_norm_le' (f : V₁ ->+ V₂) {C : Real} (h : forall x, ‖f 
x‖ <= C * ‖x‖) : ‖f.mkNormedAddGroupHom C h‖ <= max C 0
参数：f : V₁ ->+ V₂；h : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
If a bounded group homomorphism map is constructed from a group homomorphism
via the constructor `AddMonoidHom.mkNormedAddGroupHom`, then its norm is bounded
 by the bound
given to the constructor or zero if this bound is negative.
-/
theorem mkNormedAddGroupHom_norm_le' (f : V₁ →+ V₂) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkNormedAddGroupHom C h‖ ≤ max C 0 :=
  opNorm_le_bound _ (le_max_right _ _) fun x =>
    (h x).trans <| by gcongr; apply le_max_left

alias _root_.AddMonoidHom.mkNormedAddGroupHom_norm_le := mkNormedAddGroupHom_norm_le

alias _root_.AddMonoidHom.mkNormedAddGroupHom_norm_le' := mkNormedAddGroupHom_norm_le'

/-! ### Addition of normed group homs -/


/-- Addition of normed group homs. -/
/-
**NormedAddGroupHom.add** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：add : Add (NormedAddGroupHom V₁ V₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Addition of normed group homs.
-/
instance add : Add (NormedAddGroupHom V₁ V₂) :=
  ⟨fun f g =>
    (f.toAddMonoidHom + g.toAddMonoidHom).mkNormedAddGroupHom (‖f‖ + ‖g‖) fun v =>
      calc
        ‖f v + g v‖ ≤ ‖f v‖ + ‖g v‖ := norm_add_le _ _
        _ ≤ ‖f‖ * ‖v‖ + ‖g‖ * ‖v‖ := by gcongr <;> apply le_opNorm
        _ = (‖f‖ + ‖g‖) * ‖v‖ := by rw [add_mul]
        ⟩

/-- The operator norm satisfies the triangle inequality. -/
/-
**NormedAddGroupHom.opNorm_add_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：opNorm_add_le : ‖f + g‖ <= ‖f‖ + ‖g‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.mkNormedAddGroupHom_norm_le`：mkNormedAddGroupHom_norm_
le (f : V₁ ->+ V₂) {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖
f.mkNormedAddGroupHom C h‖ <= C
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NormedAddGroupHom.opNorm_nonneg`：opNorm_nonneg : 0 <= ‖f‖

--- 原说明 ---
The operator norm satisfies the triangle inequality.
-/
theorem opNorm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  mkNormedAddGroupHom_norm_le _ (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _)) _

@[simp]
/-
**NormedAddGroupHom.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_add (f g : NormedAddGroupHom V₁ V₂) : ⇑(f + g) = f + g
参数：f g : NormedAddGroupHom V₁ V₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (f g : NormedAddGroupHom V₁ V₂) : ⇑(f + g) = f + g :=
  rfl

@[simp]
/-
**NormedAddGroupHom.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：add_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) : (f + g) v = f v + g v
参数：f g : NormedAddGroupHom V₁ V₂；v : V₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
    (f + g) v = f v + g v :=
  rfl

/-! ### The zero normed group hom -/


/-
**NormedAddGroupHom.zero** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：zero : Zero (NormedAddGroupHom V₁ V₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### The zero normed group hom
-/
instance zero : Zero (NormedAddGroupHom V₁ V₂) :=
  ⟨(0 : V₁ →+ V₂).mkNormedAddGroupHom 0 (by simp)⟩
/-
**NormedAddGroupHom.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：inhabited : Inhabited (NormedAddGroupHom V₁ V₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (NormedAddGroupHom V₁ V₂) :=
  ⟨0⟩

/-- The norm of the `0` operator is `0`. -/
/-
**NormedAddGroupHom.opNorm_zero** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：opNorm_zero : ‖(0 : NormedAddGroupHom V₁ V₂)‖ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `NormedAddGroupHom.bounds_bddBelow`：bounds_bddBelow {f : NormedAddGroupHo
m V₁ V₂} : BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `NormedAddGroupHom.opNorm_nonneg`：opNorm_nonneg : 0 <= ‖f‖

--- 原说明 ---
The norm of the `0` operator is `0`.
-/
theorem opNorm_zero : ‖(0 : NormedAddGroupHom V₁ V₂)‖ = 0 :=
  le_antisymm
    (csInf_le bounds_bddBelow
      ⟨ge_of_eq rfl, fun _ =>
        le_of_eq
          (by
            rw [zero_mul]
            exact norm_zero)⟩)
    (opNorm_nonneg _)

/-- For normed groups, an operator is zero iff its norm vanishes. -/
/-
**NormedAddGroupHom.opNorm_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
`。
形式化陈述：opNorm_zero_iff {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGrou
p V₂] {f : NormedAddGroupHom V₁ V₂} : ‖f‖ = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `NormedAddGroupHom.le_opNorm`：le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `NormedAddGroupHom.opNorm_zero`：opNorm_zero : ‖(0 : NormedAddGroupHom V₁ 
V₂)‖ = 0

--- 原说明 ---
For normed groups, an operator is zero iff its norm vanishes.
-/
theorem opNorm_zero_iff {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
    {f : NormedAddGroupHom V₁ V₂} : ‖f‖ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn =>
      ext fun x =>
        norm_le_zero_iff.1
          (calc
            _ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
            _ = _ := by rw [hn, zero_mul]))
    fun hf => by rw [hf, opNorm_zero]

@[simp]
/-
**NormedAddGroupHom.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_zero : ⇑(0 : NormedAddGroupHom V₁ V₂) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : NormedAddGroupHom V₁ V₂) = 0 :=
  rfl

@[simp]
/-
**NormedAddGroupHom.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：zero_apply (v : V₁) : (0 : NormedAddGroupHom V₁ V₂) v = 0
参数：v : V₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (v : V₁) : (0 : NormedAddGroupHom V₁ V₂) v = 0 :=
  rfl

variable {f g}

/-! ### The identity normed group hom -/


variable (V)

/-- The identity as a continuous normed group hom. -/
@[simps!]
/-
**NormedAddGroupHom.id** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：id : NormedAddGroupHom V V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a continuous normed group hom.
-/
def id : NormedAddGroupHom V V :=
  (AddMonoidHom.id V).mkNormedAddGroupHom 1 (by simp)

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the norm of every
element vanishes, where it is `0`. (Since we are working with seminorms this can happen even if the
space is non-trivial.) It means that one cannot do better than an inequality in general. -/
/-
**NormedAddGroupHom.norm_id_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：norm_id_le : ‖(id V : NormedAddGroupHom V V)‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.id_apply`：∀ (V : Type u_1) [inst : SeminormedAddCommGr
oup V] (a : V), (NormedAddGroupHom.id V) a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The norm of the identity is at most `1`. It is in fact `1`, except when the norm
 of every
element vanishes, where it is `0`. (Since we are working with seminorms this can
 happen even if the
space is non-trivial.) It means that one cannot do better than an inequality in 
general.
-/
theorem norm_id_le : ‖(id V : NormedAddGroupHom V V)‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by simp

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
@[simp]
/-
**NormedAddGroupHom.norm_id** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：norm_id [NontrivialTopology V] : ‖id V‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NormedAddGroupHom.norm_id_le`：norm_id_le : ‖(id V : NormedAddGroupHom V 
V)‖ <= 1
· 使用定理 `exists_norm_ne_zero`：∀ (E : Type u_5) [inst : SeminormedAddGroup E] [Non
trivialTopology E], ∃ x, ‖x‖ ≠ 0
· 使用定理 `NormedAddGroupHom.ratio_le_opNorm`：ratio_le_opNorm (x : V₁) : ‖f x‖ / ‖x
‖ <= ‖f‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `NormedAddGroupHom.id_apply`：∀ (V : Type u_1) [inst : SeminormedAddCommGr
oup V] (a : V), (NormedAddGroupHom.id V) a = a

--- 原说明 ---
If a normed space is non-trivial, then the norm of the identity equals `1`.
-/
theorem norm_id [NontrivialTopology V] : ‖id V‖ = 1 :=
  le_antisymm (norm_id_le V) <| by
    let ⟨x, hx⟩ := exists_norm_ne_zero V
    have := (id V).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this
/-
**NormedAddGroupHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_id : (NormedAddGroupHom.id V : V -> V) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : (NormedAddGroupHom.id V : V → V) = _root_.id :=
  rfl

/-! ### The negation of a normed group hom -/


/-- Opposite of a normed group hom. -/
/-
**NormedAddGroupHom.neg** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：neg : Neg (NormedAddGroupHom V₁ V₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Opposite of a normed group hom.
-/
instance neg : Neg (NormedAddGroupHom V₁ V₂) :=
  ⟨fun f => (-f.toAddMonoidHom).mkNormedAddGroupHom ‖f‖ fun v => by simp [le_opNorm f v]⟩

@[simp]
/-
**NormedAddGroupHom.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_neg (f : NormedAddGroupHom V₁ V₂) : ⇑(-f) = -f
参数：f : NormedAddGroupHom V₁ V₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (f : NormedAddGroupHom V₁ V₂) : ⇑(-f) = -f :=
  rfl

@[simp]
/-
**NormedAddGroupHom.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：neg_apply (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (-f : NormedAddGroupHom
 V₁ V₂) v = -f v
参数：f : NormedAddGroupHom V₁ V₂；v : V₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (f : NormedAddGroupHom V₁ V₂) (v : V₁) :
    (-f : NormedAddGroupHom V₁ V₂) v = -f v :=
  rfl
/-
**NormedAddGroupHom.opNorm_neg** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：opNorm_neg (f : NormedAddGroupHom V₁ V₂) : ‖-f‖ = ‖f‖
参数：f : NormedAddGroupHom V₁ V₂。
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opNorm_neg (f : NormedAddGroupHom V₁ V₂) : ‖-f‖ = ‖f‖ := by
  simp only [norm_def, coe_neg, norm_neg, Pi.neg_apply]

/-! ### Subtraction of normed group homs -/


/-- Subtraction of normed group homs. -/
/-
**NormedAddGroupHom.sub** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：sub : Sub (NormedAddGroupHom V₁ V₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtraction of normed group homs.
-/
instance sub : Sub (NormedAddGroupHom V₁ V₂) :=
  ⟨fun f g =>
    { f.toAddMonoidHom - g.toAddMonoidHom with
      bound' := by
        simp only [AddMonoidHom.toFun_eq_coe, sub_eq_add_neg]
        exact (f + -g).bound' }⟩

@[simp]
/-
**NormedAddGroupHom.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_sub (f g : NormedAddGroupHom V₁ V₂) : ⇑(f - g) = f - g
参数：f g : NormedAddGroupHom V₁ V₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (f g : NormedAddGroupHom V₁ V₂) : ⇑(f - g) = f - g :=
  rfl

@[simp]
/-
**NormedAddGroupHom.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：sub_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) : (f - g : NormedAddGro
upHom V₁ V₂) v = f v - g v
参数：f g : NormedAddGroupHom V₁ V₂；v : V₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
    (f - g : NormedAddGroupHom V₁ V₂) v = f v - g v :=
  rfl

/-! ### Scalar actions on normed group homs -/


section SMul

variable {R R' : Type*} [MonoidWithZero R] [DistribMulAction R V₂] [PseudoMetricSpace R]
  [IsBoundedSMul R V₂] [MonoidWithZero R'] [DistribMulAction R' V₂] [PseudoMetricSpace R']
  [IsBoundedSMul R' V₂]

/-
**NormedAddGroupHom.smul** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：smul : SMul R (NormedAddGroupHom V₁ V₂) where smul r f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul : SMul R (NormedAddGroupHom V₁ V₂) where
  smul r f :=
    { toFun := r • ⇑f
      map_add' := (r • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨dist r 0 * b, fun x => by
          have := dist_smul_pair r (f x) (f 0)
          rw [map_zero, smul_zero, dist_zero_right, dist_zero_right] at this
          rw [mul_assoc]
          refine this.trans ?_
          gcongr
          exact hb x⟩ }

@[simp]
/-
**NormedAddGroupHom.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_smul (r : R) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • ⇑f
参数：r : R；f : NormedAddGroupHom V₁ V₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (r : R) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
/-
**NormedAddGroupHom.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：smul_apply (r : R) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r 
• f v
参数：r : R；f : NormedAddGroupHom V₁ V₂；v : V₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (r : R) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
  rfl
/-
**NormedAddGroupHom.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：smulCommClass [SMulCommClass R R' V₂] : SMulCommClass R R' (NormedAddGroup
Hom V₁ V₂) where smul_comm _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass [SMulCommClass R R' V₂] :
    SMulCommClass R R' (NormedAddGroupHom V₁ V₂) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _
/-
**NormedAddGroupHom.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：isScalarTower [SMul R R'] [IsScalarTower R R' V₂] : IsScalarTower R R' (No
rmedAddGroupHom V₁ V₂) where smul_assoc _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower [SMul R R'] [IsScalarTower R R' V₂] :
    IsScalarTower R R' (NormedAddGroupHom V₁ V₂) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _
/-
**NormedAddGroupHom.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom
`。
形式化陈述：isCentralScalar [DistribMulAction Rᵐᵒᵖ V₂] [IsCentralScalar R V₂] : IsCent
ralScalar R (NormedAddGroupHom V₁ V₂) where op_smul_eq_smul _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance isCentralScalar [DistribMulAction Rᵐᵒᵖ V₂] [IsCentralScalar R V₂] :
    IsCentralScalar R (NormedAddGroupHom V₁ V₂) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

end SMul

/-
**NormedAddGroupHom.nsmul** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：nsmul : SMul Nat (NormedAddGroupHom V₁ V₂) where smul n f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nsmul : SMul ℕ (NormedAddGroupHom V₁ V₂) where
  smul n f :=
    { toFun := n • ⇑f
      map_add' := (n • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨n • b, fun v => by
          rw [Pi.smul_apply, nsmul_eq_mul, mul_assoc]
          exact norm_nsmul_le.trans (by gcongr; apply hb)⟩ }

@[simp]
/-
**NormedAddGroupHom.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_nsmul (r : Nat) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • ⇑f
参数：r : Nat；f : NormedAddGroupHom V₁ V₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nsmul (r : ℕ) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
/-
**NormedAddGroupHom.nsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：nsmul_apply (r : Nat) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v =
 r • f v
参数：r : Nat；f : NormedAddGroupHom V₁ V₂；v : V₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nsmul_apply (r : ℕ) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
  rfl
/-
**NormedAddGroupHom.zsmul** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：zsmul : SMul Int (NormedAddGroupHom V₁ V₂) where smul z f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance zsmul : SMul ℤ (NormedAddGroupHom V₁ V₂) where
  smul z f :=
    { toFun := z • ⇑f
      map_add' := (z • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨‖z‖ • b, fun v => by
          rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
          exact (norm_zsmul_le _ _).trans (by gcongr; apply hb)⟩ }

@[simp]
/-
**NormedAddGroupHom.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_zsmul (r : Int) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • ⇑f
参数：r : Int；f : NormedAddGroupHom V₁ V₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zsmul (r : ℤ) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
/-
**NormedAddGroupHom.zsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：zsmul_apply (r : Int) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v =
 r • f v
参数：r : Int；f : NormedAddGroupHom V₁ V₂；v : V₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zsmul_apply (r : ℤ) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
  rfl

/-! ### Normed group structure on normed group homs -/


/-- Homs between two given normed groups form a commutative additive group. -/
/-
**NormedAddGroupHom.toAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`
。
形式化陈述：toAddCommGroup : AddCommGroup (NormedAddGroupHom V₁ V₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.coe_injective`：coe_injective : @Function.Injective (No
rmedAddGroupHom V₁ V₂) (V₁ -> V₂) toFun

--- 原说明 ---
Homs between two given normed groups form a commutative additive group.
-/
instance toAddCommGroup : AddCommGroup (NormedAddGroupHom V₁ V₂) :=
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

/-- Normed group homomorphisms themselves form a seminormed group with respect to
the operator norm. -/
/-
**NormedAddGroupHom.toSeminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `NormedAd
dGroupHom`。
形式化陈述：toSeminormedAddCommGroup : SeminormedAddCommGroup (NormedAddGroupHom V₁ V₂
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_zero`：opNorm_zero : ‖(0 : NormedAddGroupHom V₁ 
V₂)‖ = 0
· 使用定理 `NormedAddGroupHom.opNorm_add_le`：opNorm_add_le : ‖f + g‖ <= ‖f‖ + ‖g‖
· 使用定理 `NormedAddGroupHom.opNorm_neg`：opNorm_neg (f : NormedAddGroupHom V₁ V₂) :
 ‖-f‖ = ‖f‖

--- 原说明 ---
Normed group homomorphisms themselves form a seminormed group with respect to
the operator norm.
-/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (NormedAddGroupHom V₁ V₂) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := opNorm
      map_zero' := opNorm_zero
      neg' := opNorm_neg
      add_le' := opNorm_add_le }

/-- Normed group homomorphisms themselves form a normed group with respect to
the operator norm. -/
/-
**NormedAddGroupHom.toNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGro
upHom`。
形式化陈述：toNormedAddCommGroup {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCom
mGroup V₂] : NormedAddCommGroup (NormedAddGroupHom V₁ V₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed group homomorphisms themselves form a normed group with respect to
the operator norm.
-/
instance toNormedAddCommGroup {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] :
    NormedAddCommGroup (NormedAddGroupHom V₁ V₂) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := opNorm
      map_zero' := opNorm_zero
      neg' := opNorm_neg
      add_le' := opNorm_add_le
      eq_zero_of_map_eq_zero' := fun _f => opNorm_zero_iff.1 }

/-- Coercion of a `NormedAddGroupHom` is an `AddMonoidHom`. Similar to `AddMonoidHom.coeFn`. -/
@[simps]
/-
**NormedAddGroupHom.coeAddHom** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coeAddHom : NormedAddGroupHom V₁ V₂ ->+ V₁ -> V₂ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.coe_zero`：coe_zero : ⇑(0 : NormedAddGroupHom V₁ V₂) = 
0
· 使用定理 `NormedAddGroupHom.coe_add`：coe_add (f g : NormedAddGroupHom V₁ V₂) : ⇑(f
 + g) = f + g

--- 原说明 ---
Coercion of a `NormedAddGroupHom` is an `AddMonoidHom`. Similar to `AddMonoidHom
.coeFn`.
-/
def coeAddHom : NormedAddGroupHom V₁ V₂ →+ V₁ → V₂ where
  toFun := DFunLike.coe
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/-
**NormedAddGroupHom.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_sum {ι : Type*} (s : Finset ι) (f : ι -> NormedAddGroupHom V₁ V₂) : ⇑(
∑ i in s, f i) = ∑ i in s, (f i : V₁ -> V₂)
参数：s : Finset ι；f : ι -> NormedAddGroupHom V₁ V₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → NormedAddGroupHom V₁ V₂) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, (f i : V₁ → V₂) :=
  map_sum coeAddHom f s
/-
**NormedAddGroupHom.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：sum_apply {ι : Type*} (s : Finset ι) (f : ι -> NormedAddGroupHom V₁ V₂) (v
 : V₁) : (∑ i in s, f i) v = ∑ i in s, f i v
参数：s : Finset ι；f : ι -> NormedAddGroupHom V₁ V₂；v : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NormedAddGroupHom.coe_sum`：coe_sum {ι : Type*} (s : Finset ι) (f : ι -> 
NormedAddGroupHom V₁ V₂) : ⇑(∑ i in s, f i) = ∑ i in s, (f i : V₁ -> V₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → NormedAddGroupHom V₁ V₂) (v : V₁) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v := by simp only [coe_sum, Finset.sum_apply]

/-! ### Module structure on normed group homs -/


/-
**NormedAddGroupHom.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHo
m`。
形式化陈述：distribMulAction {R : Type*} [MonoidWithZero R] [DistribMulAction R V₂] [P
seudoMetricSpace R] [IsBoundedSMul R V₂] : DistribMulAction R (NormedAddGroupHom
 V₁ V₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.coe_injective`：coe_injective : @Function.Injective (No
rmedAddGroupHom V₁ V₂) (V₁ -> V₂) toFun
· 使用定理 `NormedAddGroupHom.coe_smul`：coe_smul (r : R) (f : NormedAddGroupHom V₁ V
₂) : ⇑(r • f) = r • ⇑f

--- 原说明 ---
### Module structure on normed group homs
-/
instance distribMulAction {R : Type*} [MonoidWithZero R] [DistribMulAction R V₂]
    [PseudoMetricSpace R] [IsBoundedSMul R V₂] : DistribMulAction R (NormedAddGroupHom V₁ V₂) :=
  Function.Injective.distribMulAction coeAddHom coe_injective coe_smul
/-
**NormedAddGroupHom.module** 是 Mathlib 中的一个实例，位于命名空间 `NormedAddGroupHom`。
形式化陈述：module {R : Type*} [Semiring R] [Module R V₂] [PseudoMetricSpace R] [IsBou
ndedSMul R V₂] : Module R (NormedAddGroupHom V₁ V₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.coe_injective`：coe_injective : @Function.Injective (No
rmedAddGroupHom V₁ V₂) (V₁ -> V₂) toFun
-/
instance module {R : Type*} [Semiring R] [Module R V₂] [PseudoMetricSpace R] [IsBoundedSMul R V₂] :
    Module R (NormedAddGroupHom V₁ V₂) :=
  Function.Injective.module _ coeAddHom coe_injective coe_smul

/-! ### Composition of normed group homs -/


/-- The composition of continuous normed group homs. -/
@[simps!]
/-
**NormedAddGroupHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：{V₁ : Type u_2} →   {V₂ : Type u_3} →     {V₃ : Type u_4} →       [inst : 
SeminormedAddCommGroup V₁] →         [inst_1 : SeminormedAddCommGroup V₂] →     
      [inst_2 : SeminormedAddCommGroup V₃] →             NormedAddGroupHom V₂ V₃
 → NormedAddGroupHom V₁ V₂ → NormedAddGroupHom V₁ V₃
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of continuous normed group homs.
-/
protected def comp (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
    NormedAddGroupHom V₁ V₃ :=
  (g.toAddMonoidHom.comp f.toAddMonoidHom).mkNormedAddGroupHom (‖g‖ * ‖f‖) fun v =>
    calc
      ‖g (f v)‖ ≤ ‖g‖ * ‖f v‖ := le_opNorm _ _
      _ ≤ ‖g‖ * (‖f‖ * ‖v‖) := by gcongr; apply le_opNorm
      _ = ‖g‖ * ‖f‖ * ‖v‖ := by rw [mul_assoc]
/-
**NormedAddGroupHom.norm_comp_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：norm_comp_le (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
 ‖g.comp f‖ <= ‖g‖ * ‖f‖
参数：g : NormedAddGroupHom V₂ V₃；f : NormedAddGroupHom V₁ V₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.mkNormedAddGroupHom_norm_le`：mkNormedAddGroupHom_norm_
le (f : V₁ ->+ V₂) {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖
f.mkNormedAddGroupHom C h‖ <= C
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_comp_le (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
    ‖g.comp f‖ ≤ ‖g‖ * ‖f‖ :=
  mkNormedAddGroupHom_norm_le _ (by positivity) _
/-
**NormedAddGroupHom.norm_comp_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroup
Hom`。
形式化陈述：norm_comp_le_of_le {g : NormedAddGroupHom V₂ V₃} {C₁ C₂ : Real} (hg : ‖g‖ 
<= C₂) (hf : ‖f‖ <= C₁) : ‖g.comp f‖ <= C₂ * C₁
参数：hg : ‖g‖ <= C₂；hf : ‖f‖ <= C₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `NormedAddGroupHom.norm_comp_le`：norm_comp_le (g : NormedAddGroupHom V₂ V
₃) (f : NormedAddGroupHom V₁ V₂) : ‖g.comp f‖ <= ‖g‖ * ‖f‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_comp_le_of_le {g : NormedAddGroupHom V₂ V₃} {C₁ C₂ : ℝ} (hg : ‖g‖ ≤ C₂)
    (hf : ‖f‖ ≤ C₁) : ‖g.comp f‖ ≤ C₂ * C₁ :=
  le_trans (norm_comp_le g f) <| by gcongr; exact le_trans (norm_nonneg _) hg
/-
**NormedAddGroupHom.norm_comp_le_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGrou
pHom`。
形式化陈述：norm_comp_le_of_le' {g : NormedAddGroupHom V₂ V₃} (C₁ C₂ C₃ : Real) (h : C
₃ = C₂ * C₁) (hg : ‖g‖ <= C₂) (hf : ‖f‖ <= C₁) : ‖g.comp f‖ <= C₃
参数：C₁ C₂ C₃ : Real；h : C₃ = C₂ * C₁；hg : ‖g‖ <= C₂；hf : ‖f‖ <= C₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.norm_comp_le_of_le`：norm_comp_le_of_le {g : NormedAddG
roupHom V₂ V₃} {C₁ C₂ : Real} (hg : ‖g‖ <= C₂) (hf : ‖f‖ <= C₁) : ‖g.comp f‖ <= 
C₂ * C₁
-/
theorem norm_comp_le_of_le' {g : NormedAddGroupHom V₂ V₃} (C₁ C₂ C₃ : ℝ) (h : C₃ = C₂ * C₁)
    (hg : ‖g‖ ≤ C₂) (hf : ‖f‖ ≤ C₁) : ‖g.comp f‖ ≤ C₃ := by
  rw [h]
  exact norm_comp_le_of_le hg hf

/-- Composition of normed groups hom as an additive group morphism. -/
/-
**NormedAddGroupHom.compHom** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：compHom : NormedAddGroupHom V₂ V₃ ->+ NormedAddGroupHom V₁ V₂ ->+ NormedAd
dGroupHom V₁ V₃
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of normed groups hom as an additive group morphism.
-/
def compHom : NormedAddGroupHom V₂ V₃ →+ NormedAddGroupHom V₁ V₂ →+ NormedAddGroupHom V₁ V₃ :=
  AddMonoidHom.mk'
    (fun g =>
      AddMonoidHom.mk' (fun f => g.comp f)
        (by
          intros
          ext
          exact map_add g _ _))
    (by
      intros
      ext
      simp only [comp_apply, Pi.add_apply, AddMonoidHom.add_apply,
        AddMonoidHom.mk'_apply, coe_add])

@[simp]
/-
**NormedAddGroupHom.comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：comp_zero (f : NormedAddGroupHom V₂ V₃) : f.comp (0 : NormedAddGroupHom V₁
 V₂) = 0
参数：f : NormedAddGroupHom V₂ V₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
-/
theorem comp_zero (f : NormedAddGroupHom V₂ V₃) : f.comp (0 : NormedAddGroupHom V₁ V₂) = 0 := by
  ext
  exact map_zero f

@[simp]
/-
**NormedAddGroupHom.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：zero_comp (f : NormedAddGroupHom V₁ V₂) : (0 : NormedAddGroupHom V₂ V₃).co
mp f = 0
参数：f : NormedAddGroupHom V₁ V₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
-/
theorem zero_comp (f : NormedAddGroupHom V₁ V₂) : (0 : NormedAddGroupHom V₂ V₃).comp f = 0 := by
  ext
  rfl
/-
**NormedAddGroupHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：comp_assoc {V₄ : Type*} [SeminormedAddCommGroup V₄] (h : NormedAddGroupHom
 V₃ V₄) (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) : (h.comp g)
.comp f = h.comp (g.comp f)
参数：h : NormedAddGroupHom V₃ V₄；g : NormedAddGroupHom V₂ V₃；f : NormedAddGroupHom
 V₁ V₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
-/
theorem comp_assoc {V₄ : Type*} [SeminormedAddCommGroup V₄] (h : NormedAddGroupHom V₃ V₄)
    (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl
/-
**NormedAddGroupHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_comp (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃) : (g.
comp f : V₁ -> V₃) = (g : V₂ -> V₃) ∘ (f : V₁ -> V₂)
参数：f : NormedAddGroupHom V₁ V₂；g : NormedAddGroupHom V₂ V₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃) :
    (g.comp f : V₁ → V₃) = (g : V₂ → V₃) ∘ (f : V₁ → V₂) :=
  rfl

end NormedAddGroupHom

namespace NormedAddGroupHom

variable {V W V₁ V₂ V₃ : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
  [SeminormedAddCommGroup V₁] [SeminormedAddCommGroup V₂] [SeminormedAddCommGroup V₃]

/-- The inclusion of an `AddSubgroup`, as bounded group homomorphism. -/
@[simps!]
/-
**NormedAddGroupHom.incl** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：incl (s : AddSubgroup V) : NormedAddGroupHom s V where toFun
参数：s : AddSubgroup V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of an `AddSubgroup`, as bounded group homomorphism.
-/
def incl (s : AddSubgroup V) : NormedAddGroupHom s V where
  toFun := (Subtype.val : s → V)
  map_add' _ _ := AddSubgroup.coe_add _ _ _
  bound' := ⟨1, fun v => by rw [one_mul, AddSubgroup.coe_norm]⟩
/-
**NormedAddGroupHom.norm_incl** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：norm_incl {V' : AddSubgroup V} (x : V') : ‖incl _ x‖ = ‖x‖
参数：x : V'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_incl {V' : AddSubgroup V} (x : V') : ‖incl _ x‖ = ‖x‖ :=
  rfl

/-!### Kernel -/


section Kernels

variable (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃)

/-- The kernel of a bounded group homomorphism. Naturally endowed with a
`SeminormedAddCommGroup` instance. -/
/-
**NormedAddGroupHom.ker** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：ker : AddSubgroup V₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a bounded group homomorphism. Naturally endowed with a
`SeminormedAddCommGroup` instance.
-/
def ker : AddSubgroup V₁ :=
  f.toAddMonoidHom.ker
/-
**NormedAddGroupHom.mem_ker** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：mem_ker (v : V₁) : v in f.ker ↔ f v = 0
参数：v : V₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroupHom.ker.eq_1`：∀ {V₁ : Type u_3} {V₂ : Type u_4} [inst : Se
minormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : NormedAddGr
oupHom V₁ V₂), f…
· 使用定理 `AddMonoidHom.mem_ker`：∀ {G : Type u_1} [inst : AddGroup G] {M : Type u_7
} [inst_1 : AddZeroClass M] {f : G →+ M} {x : G}, x ∈ f.ker ↔ f x = 0
· 使用定理 `NormedAddGroupHom.coe_toAddMonoidHom`：coe_toAddMonoidHom : ⇑f.toAddMonoi
dHom = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ker (v : V₁) : v ∈ f.ker ↔ f v = 0 := by
  rw [ker, f.toAddMonoidHom.mem_ker, coe_toAddMonoidHom]

/-- Given a normed group hom `f : V₁ → V₂` satisfying `g.comp f = 0` for some `g : V₂ → V₃`,
the corestriction of `f` to the kernel of `g`. -/
@[simps]
/-
**NormedAddGroupHom.ker.lift** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom.ker`。
形式化陈述：{V₁ : Type u_3} →   {V₂ : Type u_4} →     {V₃ : Type u_5} →       [inst : 
SeminormedAddCommGroup V₁] →         [inst_1 : SeminormedAddCommGroup V₂] →     
      [inst_2 : SeminormedAddCommGroup V₃] →             (f : NormedAddGroupHom 
V₁ V₂) → (g : NormedAddGroupHom V₂ V₃) → g.comp f = 0 → NormedAddGroupHom V₁ ↥g.
ker
参数：f : NormedAddGroupHom V₁ V₂；g : NormedAddGroupHom V₂ V₃。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.bound'`：∀ {V : Type u_1} {W : Type u_2} [inst : Semino
rmedAddCommGroup V] [inst_1 : SeminormedAddCommGroup W]   (self : NormedAddGroup
Hom V W), ∃ C,…

--- 原说明 ---
Given a normed group hom `f : V₁ → V₂` satisfying `g.comp f = 0` for some `g : V
₂ → V₃`,
the corestriction of `f` to the kernel of `g`.
-/
def ker.lift (h : g.comp f = 0) : NormedAddGroupHom V₁ g.ker where
  toFun v := ⟨f v, by rw [g.mem_ker, ← comp_apply g f, h, zero_apply]⟩
  map_add' v w := by simp only [map_add, AddMemClass.mk_add_mk]
  bound' := f.bound'

@[simp]
/-
**NormedAddGroupHom.ker.incl_comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroup
Hom.ker`。
形式化陈述：∀ {V₁ : Type u_3} {V₂ : Type u_4} {V₃ : Type u_5} [inst : SeminormedAddCom
mGroup V₁]   [inst_1 : SeminormedAddCommGroup V₂] [inst_2 : SeminormedAddCommGro
up V₃] (f : NormedAddGroupHom V₁ V₂)   (g : NormedAddGroupHom V₂ V₃) (h : g.comp
 f = 0),   (NormedAddGroupHom.incl g.ker).comp (NormedAddGroupHom.ker.lift f g h
) = f
参数：f : NormedAddGroupHom V₁ V₂；g : NormedAddGroupHom V₂ V₃；h : g.comp f = 0；Norm
edAddGroupHom.incl g.ker；NormedAddGroupHom.ker.lift f g h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
-/
theorem ker.incl_comp_lift (h : g.comp f = 0) : (incl g.ker).comp (ker.lift f g h) = f := by
  ext
  rfl

@[simp]
/-
**NormedAddGroupHom.ker_zero** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：ker_zero : (0 : NormedAddGroupHom V₁ V₂).ker = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_zero : (0 : NormedAddGroupHom V₁ V₂).ker = ⊤ := by
  ext
  simp [mem_ker]
/-
**NormedAddGroupHom.coe_ker** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：coe_ker : (f.ker : Set V₁) = (f : V₁ -> V₂) ⁻¹' {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ker : (f.ker : Set V₁) = (f : V₁ → V₂) ⁻¹' {0} :=
  rfl
/-
**NormedAddGroupHom.isClosed_ker** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：isClosed_ker {V₂ : Type*} [NormedAddCommGroup V₂] (f : NormedAddGroupHom V
₁ V₂) : IsClosed (f.ker : Set V₁)
参数：f : NormedAddGroupHom V₁ V₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `NormedAddGroupHom.continuous`：∀ {V₁ : Type u_2} {V₂ : Type u_3} [inst : 
SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂]   (f : NormedAdd
GroupHom V₁ V₂), C…
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedAddGroupHom.coe_ker`：coe_ker : (f.ker : Set V₁) = (f : V₁ -> V₂) ⁻
¹' {0}
-/
theorem isClosed_ker {V₂ : Type*} [NormedAddCommGroup V₂] (f : NormedAddGroupHom V₁ V₂) :
    IsClosed (f.ker : Set V₁) :=
  f.coe_ker ▸ IsClosed.preimage f.continuous (T1Space.t1 0)

end Kernels

/-! ### Range -/


section Range

variable (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃)

/-- The image of a bounded group homomorphism. Naturally endowed with a
`SeminormedAddCommGroup` instance. -/
/-
**NormedAddGroupHom.range** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：range : AddSubgroup V₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a bounded group homomorphism. Naturally endowed with a
`SeminormedAddCommGroup` instance.
-/
def range : AddSubgroup V₂ :=
  f.toAddMonoidHom.range
/-
**NormedAddGroupHom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：mem_range (v : V₂) : v in f.range ↔ exists w, f w = v
参数：v : V₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range (v : V₂) : v ∈ f.range ↔ ∃ w, f w = v := Iff.rfl

@[simp]
/-
**NormedAddGroupHom.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`
。
形式化陈述：mem_range_self (v : V₁) : f v in f.range
参数：v : V₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_range_self (v : V₁) : f v ∈ f.range :=
  ⟨v, rfl⟩
/-
**NormedAddGroupHom.comp_range** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：comp_range : (g.comp f).range = AddSubgroup.map g.toAddMonoidHom f.range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.map_range`：∀ {G : Type u_1} [inst : AddGroup G] {N : Type u
_5} {P : Type u_6} [inst_1 : AddGroup N] [inst_2 : AddGroup P]   (g : N →+ P) (f
 : G →+ N), …
-/
theorem comp_range : (g.comp f).range = AddSubgroup.map g.toAddMonoidHom f.range := by
  unfold range
  rw [AddMonoidHom.map_range]
  rfl
/-
**NormedAddGroupHom.incl_range** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：incl_range (s : AddSubgroup V₁) : (incl s).range = s
参数：s : AddSubgroup V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedAddGroupHom.incl_apply`：∀ {V : Type u_1} [inst : SeminormedAddComm
Group V] (s : AddSubgroup V) (self : ↥s),   (NormedAddGroupHom.incl s) self = ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem incl_range (s : AddSubgroup V₁) : (incl s).range = s := by
  ext x
  exact ⟨fun ⟨y, hy⟩ => by rw [← hy]; simp, fun hx => ⟨⟨x, hx⟩, by simp⟩⟩

@[simp]
/-
**NormedAddGroupHom.range_comp_incl_top** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGrou
pHom`。
形式化陈述：range_comp_incl_top : (f.comp (incl (⊤ : AddSubgroup V₁))).range = f.range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedAddGroupHom.comp_range`：comp_range : (g.comp f).range = AddSubgrou
p.map g.toAddMonoidHom f.range
· 使用定理 `NormedAddGroupHom.incl_range`：incl_range (s : AddSubgroup V₁) : (incl s)
.range = s
-/
theorem range_comp_incl_top : (f.comp (incl (⊤ : AddSubgroup V₁))).range = f.range := by
  simp [comp_range, incl_range, ← AddMonoidHom.range_eq_map]; rfl

end Range

variable {f : NormedAddGroupHom V W}

/-- A `NormedAddGroupHom` is *norm-nonincreasing* if `‖f v‖ ≤ ‖v‖` for all `v`. -/
/-
**NormedAddGroupHom.NormNoninc** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：NormNoninc (f : NormedAddGroupHom V W) : Prop
参数：f : NormedAddGroupHom V W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NormedAddGroupHom` is *norm-nonincreasing* if `‖f v‖ ≤ ‖v‖` for all `v`.
-/
def NormNoninc (f : NormedAddGroupHom V W) : Prop :=
  ∀ v, ‖f v‖ ≤ ‖v‖

namespace NormNoninc

/-
**NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one** 是 Mathlib 中的一个定理，位于命
名空间 `NormedAddGroupHom.NormNoninc`。
形式化陈述：normNoninc_iff_norm_le_one : f.NormNoninc ↔ ‖f‖ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `NormedAddGroupHom.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖ <
= c) (x : V₁) : ‖f x‖ <= c * ‖x‖
-/
theorem normNoninc_iff_norm_le_one : f.NormNoninc ↔ ‖f‖ ≤ 1 := by
  refine ⟨fun h => ?_, fun h => fun v => ?_⟩
  · refine opNorm_le_bound _ zero_le_one fun v => ?_
    simpa [one_mul] using h v
  · simpa using le_of_opNorm_le f h v
/-
**NormedAddGroupHom.NormNoninc.zero** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
.NormNoninc`。
形式化陈述：zero : (0 : NormedAddGroupHom V₁ V₂).NormNoninc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
-/
theorem zero : (0 : NormedAddGroupHom V₁ V₂).NormNoninc := fun v => by simp
/-
**NormedAddGroupHom.NormNoninc.id** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom.N
ormNoninc`。
形式化陈述：id : (id V).NormNoninc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem id : (id V).NormNoninc := fun _v => le_rfl
/-
**NormedAddGroupHom.NormNoninc.comp** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
.NormNoninc`。
形式化陈述：comp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : g.N
ormNoninc) (hf : f.NormNoninc) : (g.comp f).NormNoninc
参数：hg : g.NormNoninc；hf : f.NormNoninc。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem comp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : g.NormNoninc)
    (hf : f.NormNoninc) : (g.comp f).NormNoninc := fun v => (hg (f v)).trans (hf v)

@[simp]
/-
**NormedAddGroupHom.NormNoninc.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroup
Hom.NormNoninc`。
形式化陈述：neg_iff {f : NormedAddGroupHom V₁ V₂} : (-f).NormNoninc ↔ f.NormNoninc
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem neg_iff {f : NormedAddGroupHom V₁ V₂} : (-f).NormNoninc ↔ f.NormNoninc :=
  ⟨fun h x => by simpa using h x, fun h x => (norm_neg (f x)).le.trans (h x)⟩

end NormNoninc

section Isometry

/-
**NormedAddGroupHom.norm_eq_of_isometry** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGrou
pHom`。
形式化陈述：norm_eq_of_isometry {f : NormedAddGroupHom V W} (hf : Isometry f) (v : V) 
: ‖f v‖ = ‖v‖
参数：hf : Isometry f；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoidHomClass.isometry_iff_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F 
: Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [ins
t_2 : FunLike 𝓕 E F] [Add…
-/
theorem norm_eq_of_isometry {f : NormedAddGroupHom V W} (hf : Isometry f) (v : V) : ‖f v‖ = ‖v‖ :=
  (AddMonoidHomClass.isometry_iff_norm f).mp hf v
/-
**NormedAddGroupHom.isometry_id** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：isometry_id : @Isometry V V _ _ (id V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isometry_id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Isometry id
-/
theorem isometry_id : @Isometry V V _ _ (id V) :=
  _root_.isometry_id
/-
**NormedAddGroupHom.isometry_comp** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom`。
形式化陈述：isometry_comp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} 
(hg : Isometry g) (hf : Isometry f) : Isometry (g.comp f)
参数：hg : Isometry g；hf : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
-/
theorem isometry_comp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : Isometry g)
    (hf : Isometry f) : Isometry (g.comp f) :=
  hg.comp hf
/-
**NormedAddGroupHom.normNoninc_of_isometry** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddG
roupHom`。
形式化陈述：normNoninc_of_isometry (hf : Isometry f) : f.NormNoninc
参数：hf : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `NormedAddGroupHom.norm_eq_of_isometry`：norm_eq_of_isometry {f : NormedAd
dGroupHom V W} (hf : Isometry f) (v : V) : ‖f v‖ = ‖v‖
-/
theorem normNoninc_of_isometry (hf : Isometry f) : f.NormNoninc := fun v =>
  le_of_eq <| norm_eq_of_isometry hf v

end Isometry

variable {W₁ W₂ W₃ : Type*} [SeminormedAddCommGroup W₁] [SeminormedAddCommGroup W₂]
  [SeminormedAddCommGroup W₃]

variable (f) (g : NormedAddGroupHom V W)
variable {f₁ g₁ : NormedAddGroupHom V₁ W₁}
variable {f₂ g₂ : NormedAddGroupHom V₂ W₂}
variable {f₃ g₃ : NormedAddGroupHom V₃ W₃}

/-- The equalizer of two morphisms `f g : NormedAddGroupHom V W`. -/
/-
**NormedAddGroupHom.equalizer** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom`。
形式化陈述：equalizer
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer of two morphisms `f g : NormedAddGroupHom V W`.
-/
def equalizer :=
  (f - g).ker

namespace Equalizer

/-- The inclusion of `f.equalizer g` as a `NormedAddGroupHom`. -/
/-
**NormedAddGroupHom.Equalizer.** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom.Equa
lizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of `f.equalizer g` as a `NormedAddGroupHom`.
-/
def ι : NormedAddGroupHom (f.equalizer g) V :=
  incl _
/-
**NormedAddGroupHom.Equalizer.comp_** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom
.Equalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_ι_eq : f.comp (ι f g) = g.comp (ι f g) := by
  ext x
  rw [comp_apply, comp_apply, ← sub_eq_zero, ← NormedAddGroupHom.sub_apply]
  exact x.2

variable {f g}

/-- If `φ : NormedAddGroupHom V₁ V` is such that `f.comp φ = g.comp φ`, the induced morphism
`NormedAddGroupHom V₁ (f.equalizer g)`. -/
@[simps]
/-
**NormedAddGroupHom.Equalizer.lift** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom.
Equalizer`。
形式化陈述：lift (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) : NormedAddGro
upHom V₁ (f.equalizer g) where toFun v
参数：φ : NormedAddGroupHom V₁ V；h : f.comp φ = g.comp φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : NormedAddGroupHom V₁ V` is such that `f.comp φ = g.comp φ`, the induced 
morphism
`NormedAddGroupHom V₁ (f.equalizer g)`.
-/
def lift (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) :
    NormedAddGroupHom V₁ (f.equalizer g) where
  toFun v :=
    ⟨φ v,
      show (f - g) (φ v) = 0 by
        rw [NormedAddGroupHom.sub_apply, sub_eq_zero, ← comp_apply, h, comp_apply]⟩
  map_add' v₁ v₂ := by
    ext
    simp only [map_add, AddSubgroup.coe_add]
  bound' := by
    obtain ⟨C, _C_pos, hC⟩ := φ.bound
    exact ⟨C, hC⟩

@[simp]
/-
**NormedAddGroupHom.Equalizer.** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom.Equa
lizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_comp_lift (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) :
    (ι _ _).comp (lift φ h) = φ := by
  ext
  rfl

/-- The lifting property of the equalizer as an equivalence. -/
@[simps]
/-
**NormedAddGroupHom.Equalizer.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGrou
pHom.Equalizer`。
形式化陈述：liftEquiv : { φ : NormedAddGroupHom V₁ V // f.comp φ = g.comp φ } ≃ Normed
AddGroupHom V₁ (f.equalizer g) where toFun φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lifting property of the equalizer as an equivalence.
-/
def liftEquiv :
    { φ : NormedAddGroupHom V₁ V // f.comp φ = g.comp φ } ≃
      NormedAddGroupHom V₁ (f.equalizer g) where
  toFun φ := lift φ φ.prop
  invFun ψ := ⟨(ι f g).comp ψ, by rw [← comp_assoc, ← comp_assoc, comp_ι_eq]⟩
  left_inv φ := by simp

/-- Given `φ : NormedAddGroupHom V₁ V₂` and `ψ : NormedAddGroupHom W₁ W₂` such that
`ψ.comp f₁ = f₂.comp φ` and `ψ.comp g₁ = g₂.comp φ`, the induced morphism
`NormedAddGroupHom (f₁.equalizer g₁) (f₂.equalizer g₂)`. -/
/-
**NormedAddGroupHom.Equalizer.map** 是 Mathlib 中的一个定义，位于命名空间 `NormedAddGroupHom.E
qualizer`。
形式化陈述：map (φ : NormedAddGroupHom V₁ V₂) (ψ : NormedAddGroupHom W₁ W₂) (hf : ψ.co
mp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) : NormedAddGroupHom (f₁.equalize
r g₁) (f₂.equalizer g₂)
参数：φ : NormedAddGroupHom V₁ V₂；ψ : NormedAddGroupHom W₁ W₂；hf : ψ.comp f₁ = f₂.c
omp φ；hg : ψ.comp g₁ = g₂.comp φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `φ : NormedAddGroupHom V₁ V₂` and `ψ : NormedAddGroupHom W₁ W₂` such that
`ψ.comp f₁ = f₂.comp φ` and `ψ.comp g₁ = g₂.comp φ`, the induced morphism
`NormedAddGroupHom (f₁.equalizer g₁) (f₂.equalizer g₂)`.
-/
def map (φ : NormedAddGroupHom V₁ V₂) (ψ : NormedAddGroupHom W₁ W₂) (hf : ψ.comp f₁ = f₂.comp φ)
    (hg : ψ.comp g₁ = g₂.comp φ) : NormedAddGroupHom (f₁.equalizer g₁) (f₂.equalizer g₂) :=
  lift (φ.comp <| ι _ _) <| by
    simp only [← comp_assoc, ← hf, ← hg]
    simp only [comp_assoc, comp_ι_eq f₁ g₁]

variable {φ : NormedAddGroupHom V₁ V₂} {ψ : NormedAddGroupHom W₁ W₂}
variable {φ' : NormedAddGroupHom V₂ V₃} {ψ' : NormedAddGroupHom W₂ W₃}

@[simp]
/-
**NormedAddGroupHom.Equalizer.** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom.Equa
lizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) :
    (ι f₂ g₂).comp (map φ ψ hf hg) = φ.comp (ι f₁ g₁) :=
  ι_comp_lift _ _

@[simp]
/-
**NormedAddGroupHom.Equalizer.map_id** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHo
m.Equalizer`。
形式化陈述：map_id : map (f₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem map_id : map (f₂ := f₁) (g₂ := g₁) (id V₁) (id W₁) rfl rfl = id (f₁.equalizer g₁) := by
  ext
  rfl
/-
**NormedAddGroupHom.Equalizer.comm_sq** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupH
om.Equalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comm_sq₂ (hf : ψ.comp f₁ = f₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ') :
    (ψ'.comp ψ).comp f₁ = f₃.comp (φ'.comp φ) := by
  rw [comp_assoc, hf, ← comp_assoc, hf', comp_assoc]
/-
**NormedAddGroupHom.Equalizer.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddG
roupHom.Equalizer`。
形式化陈述：map_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (hf
' : ψ'.comp f₂ = f₃.comp φ') (hg' : ψ'.comp g₂ = g₃.comp φ') : (map φ' ψ' hf' hg
').comp (map φ ψ hf hg) = map (φ'.comp φ) (ψ'.comp ψ) (comm_sq₂ hf hf') (comm_sq
₂ hg hg')
参数：hf : ψ.comp f₁ = f₂.comp φ；hg : ψ.comp g₁ = g₂.comp φ；hf' : ψ'.comp f₂ = f₃.c
omp φ'；hg' : ψ'.comp g₂ = g₃.comp φ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `NormedAddGroupHom.Equalizer.comm_sq₂`：comm_sq₂ (hf : ψ.comp f₁ = f₂.comp
 φ) (hf' : ψ'.comp f₂ = f₃.comp φ') : (ψ'.comp ψ).comp f₁ = f₃.comp (φ'.comp φ)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem map_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
    (hf' : ψ'.comp f₂ = f₃.comp φ') (hg' : ψ'.comp g₂ = g₃.comp φ') :
    (map φ' ψ' hf' hg').comp (map φ ψ hf hg) =
      map (φ'.comp φ) (ψ'.comp ψ) (comm_sq₂ hf hf') (comm_sq₂ hg hg') := by
  ext
  rfl
/-
**NormedAddGroupHom.Equalizer.** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGroupHom.Equa
lizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_normNoninc : (ι f g).NormNoninc := fun _v => le_rfl

/-- The lifting of a norm nonincreasing morphism is norm nonincreasing. -/
/-
**NormedAddGroupHom.Equalizer.lift_normNoninc** 是 Mathlib 中的一个定理，位于命名空间 `NormedA
ddGroupHom.Equalizer`。
形式化陈述：lift_normNoninc (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (hφ
 : φ.NormNoninc) : (lift φ h).NormNoninc
参数：φ : NormedAddGroupHom V₁ V；h : f.comp φ = g.comp φ；hφ : φ.NormNoninc。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lifting of a norm nonincreasing morphism is norm nonincreasing.
-/
theorem lift_normNoninc (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.NormNoninc) :
    (lift φ h).NormNoninc :=
  hφ

/-- If `φ` satisfies `‖φ‖ ≤ C`, then the same is true for the lifted morphism. -/
/-
**NormedAddGroupHom.Equalizer.norm_lift_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddG
roupHom.Equalizer`。
形式化陈述：norm_lift_le (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (C : R
eal) (hφ : ‖φ‖ <= C) : ‖lift φ h‖ <= C
参数：φ : NormedAddGroupHom V₁ V；h : f.comp φ = g.comp φ；C : Real；hφ : ‖φ‖ <= C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ` satisfies `‖φ‖ ≤ C`, then the same is true for the lifted morphism.
-/
theorem norm_lift_le (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (C : ℝ) (hφ : ‖φ‖ ≤ C) :
    ‖lift φ h‖ ≤ C :=
  hφ
/-
**NormedAddGroupHom.Equalizer.map_normNoninc** 是 Mathlib 中的一个定理，位于命名空间 `NormedAd
dGroupHom.Equalizer`。
形式化陈述：map_normNoninc (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (
hφ : φ.NormNoninc) : (map φ ψ hf hg).NormNoninc
参数：hf : ψ.comp f₁ = f₂.comp φ；hg : ψ.comp g₁ = g₂.comp φ；hφ : φ.NormNoninc。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.Equalizer.lift_normNoninc`：lift_normNoninc (φ : Normed
AddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.NormNoninc) : (lift φ h).Nor
mNoninc
· 使用定理 `NormedAddGroupHom.NormNoninc.comp`：comp {g : NormedAddGroupHom V₂ V₃} {f
 : NormedAddGroupHom V₁ V₂} (hg : g.NormNoninc) (hf : f.NormNoninc) : (g.comp f)
.NormNoninc
· 使用定理 `NormedAddGroupHom.Equalizer.ι_normNoninc`：ι_normNoninc : (ι f g).NormNon
inc
-/
theorem map_normNoninc (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
    (hφ : φ.NormNoninc) : (map φ ψ hf hg).NormNoninc :=
  lift_normNoninc _ _ <| hφ.comp ι_normNoninc
/-
**NormedAddGroupHom.Equalizer.norm_map_le** 是 Mathlib 中的一个定理，位于命名空间 `NormedAddGr
oupHom.Equalizer`。
形式化陈述：norm_map_le (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (C :
 Real) (hφ : ‖φ.comp (ι f₁ g₁)‖ <= C) : ‖map φ ψ hf hg‖ <= C
参数：hf : ψ.comp f₁ = f₂.comp φ；hg : ψ.comp g₁ = g₂.comp φ；C : Real；hφ : ‖φ.comp (
ι f₁ g₁)‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.Equalizer.norm_lift_le`：norm_lift_le (φ : NormedAddGro
upHom V₁ V) (h : f.comp φ = g.comp φ) (C : Real) (hφ : ‖φ‖ <= C) : ‖lift φ h‖ <=
 C
-/
theorem norm_map_le (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (C : ℝ)
    (hφ : ‖φ.comp (ι f₁ g₁)‖ ≤ C) : ‖map φ ψ hf hg‖ ≤ C :=
  norm_lift_le _ _ _ hφ

end Equalizer

end NormedAddGroupHom

