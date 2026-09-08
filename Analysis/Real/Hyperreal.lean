/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Ring.StandardPart
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.FilterProduct

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences

We define the `Hyperreal` numbers as quotients of sequences `ℕ → ℝ` by an ultrafilter. These form
a field, and we prove some of their basic properties.

Note that most of the machinery that is usually defined for the specific purpose of non-standard
analysis (infinitesimal and infinite elements, standard parts) has been generalized to other
non-archimedean fields. In particular:

- `ArchimedeanClass` can be used to measure whether an element is infinitesimal (`0 < mk x`) or
  infinite (`mk x < 0`).
- `ArchimedeanClass.stdPart` generalizes the standard part function to a general ordered field.

## Todo

Use Łoś's Theorem `FirstOrder.Language.Ultraproduct.sentence_realize` to formalize the transfer
principle on `Hyperreal`.
-/

@[expose] public section

open ArchimedeanClass Filter Germ Topology

noncomputable section

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter. -/
/-
**Hyperreal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Hyperreal : Type
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ

--- 原说明 ---
Hyperreal numbers on the ultrafilter extending the cofinite filter.
-/
def Hyperreal : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℝ
deriving Inhabited

namespace Hyperreal

@[inherit_doc] notation "ℝ*" => Hyperreal

/-
**Hyperreal.** 是 Mathlib 中的一个实例，位于命名空间 `Hyperreal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Field ℝ* :=
  inferInstanceAs (Field (Germ _ _))
/-
**Hyperreal.** 是 Mathlib 中的一个实例，位于命名空间 `Hyperreal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder ℝ* :=
  inferInstanceAs (LinearOrder (Germ _ _))
/-
**Hyperreal.** 是 Mathlib 中的一个实例，位于命名空间 `Hyperreal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStrictOrderedRing ℝ* :=
  inferInstanceAs (IsStrictOrderedRing (Germ _ _))

/-- Natural embedding `ℝ → ℝ*`. -/
/-
**Hyperreal.ofReal** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：ℝ → ℝ*
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ

--- 原说明 ---
Natural embedding `ℝ → ℝ*`.
-/
@[coe] def ofReal : ℝ → ℝ* := const
/-
**Hyperreal.** 是 Mathlib 中的一个实例，位于命名空间 `Hyperreal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Natural embedding `ℝ → ℝ*`.
-/
instance : CoeTC ℝ ℝ* := ⟨ofReal⟩

@[simp, norm_cast]
/-
**Hyperreal.coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_eq_coe {x y : Real} : (x : Real*) = y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.const_inj`：const_inj [NeBot l] {a b : β} : (↑a : Germ l β) =
 ↑b ↔ a = b
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  Germ.const_inj
/-
**Hyperreal.coe_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_ne_coe {x y : Real} : (x : Real*) != y ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Hyperreal.coe_eq_coe`：coe_eq_coe {x y : Real} : (x : Real*) = y ↔ x = y
-/
theorem coe_ne_coe {x y : ℝ} : (x : ℝ*) ≠ y ↔ x ≠ y :=
  coe_eq_coe.not

@[simp, norm_cast]
/-
**Hyperreal.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_eq_zero {x : Real} : (x : Real*) = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.coe_eq_coe`：coe_eq_coe {x y : Real} : (x : Real*) = y ↔ x = y
-/
theorem coe_eq_zero {x : ℝ} : (x : ℝ*) = 0 ↔ x = 0 :=
  coe_eq_coe

@[simp, norm_cast]
/-
**Hyperreal.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_eq_one {x : Real} : (x : Real*) = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.coe_eq_coe`：coe_eq_coe {x y : Real} : (x : Real*) = y ↔ x = y
-/
theorem coe_eq_one {x : ℝ} : (x : ℝ*) = 1 ↔ x = 1 :=
  coe_eq_coe

@[norm_cast]
/-
**Hyperreal.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_ne_zero {x : Real} : (x : Real*) != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.coe_ne_coe`：coe_ne_coe {x y : Real} : (x : Real*) != y ↔ x != 
y
-/
theorem coe_ne_zero {x : ℝ} : (x : ℝ*) ≠ 0 ↔ x ≠ 0 :=
  coe_ne_coe

@[norm_cast]
/-
**Hyperreal.coe_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_ne_one {x : Real} : (x : Real*) != 1 ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.coe_ne_coe`：coe_ne_coe {x y : Real} : (x : Real*) != y ↔ x != 
y
-/
theorem coe_ne_one {x : ℝ} : (x : ℝ*) ≠ 1 ↔ x ≠ 1 :=
  coe_ne_coe

@[simp, norm_cast]
/-
**Hyperreal.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_one : ↑(1 : Real) = (1 : Real*)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ↑(1 : ℝ) = (1 : ℝ*) :=
  rfl

@[simp, norm_cast]
/-
**Hyperreal.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_zero : ↑(0 : Real) = (0 : Real*)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ↑(0 : ℝ) = (0 : ℝ*) :=
  rfl

@[simp, norm_cast]
/-
**Hyperreal.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_inv (x : Real) : ↑x⁻¹ = (x⁻¹ : Real*)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (x : ℝ) : ↑x⁻¹ = (x⁻¹ : ℝ*) :=
  rfl

@[simp, norm_cast]
/-
**Hyperreal.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_neg (x : Real) : ↑(-x) = (-x : Real*)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (x : ℝ) : ↑(-x) = (-x : ℝ*) :=
  rfl

@[simp, norm_cast]
/-
**Hyperreal.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_add (x y : Real) : ↑(x + y) = (x + y : Real*)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (x y : ℝ) : ↑(x + y) = (x + y : ℝ*) :=
  rfl

@[simp, norm_cast]
/-
**Hyperreal.coe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Real) : Real*) = OfNat.o
fNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℝ) : ℝ*) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
/-
**Hyperreal.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_mul (x y : Real) : ↑(x * y) = (x * y : Real*)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : ℝ) : ↑(x * y) = (x * y : ℝ*) :=
  rfl

@[simp, norm_cast]
/-
**Hyperreal.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_div (x y : Real) : ↑(x / y) = (x / y : Real*)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div (x y : ℝ) : ↑(x / y) = (x / y : ℝ*) :=
  rfl

@[simp, norm_cast]
/-
**Hyperreal.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_sub (x y : Real) : ↑(x - y) = (x - y : Real*)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (x y : ℝ) : ↑(x - y) = (x - y : ℝ*) :=
  rfl

@[simp, norm_cast]
/-
**Hyperreal.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_le_coe {x y : Real} : (x : Real*) <= y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.const_le_iff`：const_le_iff [LE β] [NeBot l] {x y : β} : (↑x 
: Germ l β) <= ↑y ↔ x <= y
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem coe_le_coe {x y : ℝ} : (x : ℝ*) ≤ y ↔ x ≤ y :=
  Germ.const_le_iff

@[simp, norm_cast]
/-
**Hyperreal.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_lt_coe {x y : Real} : (x : Real*) < y ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.const_lt_iff`：const_lt_iff [Preorder β] {x y : β} : (↑x : β*
) < ↑y ↔ x < y
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem coe_lt_coe {x y : ℝ} : (x : ℝ*) < y ↔ x < y :=
  Germ.const_lt_iff

@[simp, norm_cast]
/-
**Hyperreal.coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_nonneg {x : Real} : 0 <= (x : Real*) ↔ 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.coe_le_coe`：coe_le_coe {x y : Real} : (x : Real*) <= y ↔ x <= 
y
-/
theorem coe_nonneg {x : ℝ} : 0 ≤ (x : ℝ*) ↔ 0 ≤ x :=
  coe_le_coe

@[simp, norm_cast]
/-
**Hyperreal.coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_pos {x : Real} : 0 < (x : Real*) ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.coe_lt_coe`：coe_lt_coe {x y : Real} : (x : Real*) < y ↔ x < y
-/
theorem coe_pos {x : ℝ} : 0 < (x : ℝ*) ↔ 0 < x :=
  coe_lt_coe

@[simp, norm_cast]
/-
**Hyperreal.coe_abs** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_abs (x : Real) : ((|x| : Real) : Real*) = |↑x|
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.const_abs`：const_abs [AddCommGroup β] [LinearOrder β] (x : β
) : (↑|x| : β*) = |↑x|
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem coe_abs (x : ℝ) : ((|x| : ℝ) : ℝ*) = |↑x| :=
  const_abs x

@[simp, norm_cast]
/-
**Hyperreal.coe_max** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_max (x y : Real) : ((max x y : Real) : Real*) = max ↑x ↑y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.const_max`：const_max [LinearOrder β] (x y : β) : (↑(max x y 
: β) : β*) = max ↑x ↑y
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max ↑x ↑y :=
  Germ.const_max _ _

@[simp, norm_cast]
/-
**Hyperreal.coe_min** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_min (x y : Real) : ((min x y : Real) : Real*) = min ↑x ↑y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.const_min`：const_min [LinearOrder β] (x y : β) : (↑(min x y 
: β) : β*) = min ↑x ↑y
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min ↑x ↑y :=
  Germ.const_min _ _

/-- The canonical map `ℝ → ℝ*` as an `OrderRingHom`. -/
@[simps]
/-
**Hyperreal.coeRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：coeRingHom : Real ->+*o Real* where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `ℝ → ℝ*` as an `OrderRingHom`.
-/
def coeRingHom : ℝ →+*o ℝ* where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  monotone' _ _ := coe_le_coe.2

@[simp]
/-
**Hyperreal.archimedeanClassMk_coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：archimedeanClassMk_coe_nonneg (x : Real) : 0 <= mk (x : Real*)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.mk_map_nonneg_of_archimedean`：mk_map_nonneg_of_archimed
ean [Archimedean S] (f : S ->+*o R) (y : S) : 0 <= mk (f y)
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
-/
theorem archimedeanClassMk_coe_nonneg (x : ℝ) : 0 ≤ mk (x : ℝ*) :=
  mk_map_nonneg_of_archimedean coeRingHom x

@[simp]
/-
**Hyperreal.archimdeanClassMk_coe** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：archimdeanClassMk_coe {x : Real} (hx : x != 0) : mk (x : Real*) = 0
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.mk_map_of_archimedean'`：mk_map_of_archimedean' [Archime
dean S] (f : S ->+*o R) {x : S} (h : x != 0) : mk (f x) = 0
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
-/
theorem archimdeanClassMk_coe {x : ℝ} (hx : x ≠ 0) : mk (x : ℝ*) = 0 :=
  mk_map_of_archimedean' coeRingHom hx

@[simp]
/-
**Hyperreal.stdPart_coe** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：stdPart_coe (x : Real) : stdPart (x : Real*) = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.stdPart_map_real`：stdPart_map_real (f : Real ->+*o K) (
r : Real) : stdPart (f r) = r
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
-/
theorem stdPart_coe (x : ℝ) : stdPart (x : ℝ*) = x :=
  stdPart_map_real coeRingHom x

/-! ### Basic constants -/

/-- Construct a hyperreal number from a sequence of real numbers. -/
/-
**Hyperreal.ofSeq** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：ofSeq (f : Nat -> Real) : Real*
参数：f : Nat -> Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ

--- 原说明 ---
Construct a hyperreal number from a sequence of real numbers.
-/
def ofSeq (f : ℕ → ℝ) : ℝ* := (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℝ)
/-
**Hyperreal.ofSeq_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：ofSeq_surjective : Function.Surjective ofSeq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep
/-
**Hyperreal.ofSeq_lt_ofSeq** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：ofSeq_lt_ofSeq {f g : Nat -> Real} : ofSeq f < ofSeq g ↔ forallᶠ n in hype
rfilter Nat, f n < g n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.coe_lt`：coe_lt [Preorder β] {f g : α -> β} : (f : β*) < g ↔ 
forall* x, f x < g x
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem ofSeq_lt_ofSeq {f g : ℕ → ℝ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Germ.coe_lt
/-
**Hyperreal.ofSeq_le_ofSeq** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：ofSeq_le_ofSeq {f g : Nat -> Real} : ofSeq f <= ofSeq g ↔ forallᶠ n in hyp
erfilter Nat, f n <= g n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.coe_le`：coe_le [LE β] : (f : Germ l β) <= g ↔ f <=ᶠ[l] g
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem ofSeq_le_ofSeq {f g : ℕ → ℝ} : ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  Germ.coe_le

/-! #### ω -/

/-- A sample infinite hyperreal ω = ⟦(0, 1, 2, 3, ⋯)⟧. -/
/-
**Hyperreal.omega** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：omega : Real*
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sample infinite hyperreal ω = ⟦(0, 1, 2, 3, ⋯)⟧.
-/
def omega : ℝ* := ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hyperreal.omega
recommended_spelling "omega" for "ω" in [omega, «termω»]
/-
**Hyperreal.coe_lt_omega** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：coe_lt_omega (r : Real) : r < ω
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_lt_ofSeq`：ofSeq_lt_ofSeq {f g : Nat -> Real} : ofSeq f <
 ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n < g n
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Nat.hyperfilter_le_atTop`：↑(Filter.hyperfilter ℕ) ≤ Filter.atTop
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem coe_lt_omega (r : ℝ) : r < ω := by
  apply ofSeq_lt_ofSeq.2 <| Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop _
  obtain ⟨n, hn⟩ := exists_nat_gt r
  rw [eventually_atTop]
  exact ⟨n, fun m hm ↦ hn.trans_le (mod_cast hm)⟩
/-
**Hyperreal.omega_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：omega_pos : 0 < ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.coe_lt_omega`：coe_lt_omega (r : Real) : r < ω
-/
theorem omega_pos : 0 < ω :=
  coe_lt_omega 0

@[simp]
/-
**Hyperreal.omega_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：omega_ne_zero : ω != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Hyperreal.omega_pos`：omega_pos : 0 < ω
-/
theorem omega_ne_zero : ω ≠ 0 :=
  omega_pos.ne'

@[simp]
/-
**Hyperreal.abs_omega** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：abs_omega : |ω| = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Hyperreal.omega_pos`：omega_pos : 0 < ω
-/
theorem abs_omega : |ω| = ω :=
  abs_of_pos omega_pos

@[simp]
/-
**Hyperreal.archimedeanClassMk_omega_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：archimedeanClassMk_omega_neg : mk ω < 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Hyperreal.abs_omega`：abs_omega : |ω| = ω
· 使用定理 `Hyperreal.coe_lt_omega`：coe_lt_omega (r : Real) : r < ω
-/
theorem archimedeanClassMk_omega_neg : mk ω < 0 :=
  fun n ↦ by simpa using! coe_lt_omega n

@[simp]
/-
**Hyperreal.stdPart_omega** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：stdPart_omega : stdPart ω = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.stdPart_eq_zero`：stdPart_eq_zero {x : K} : stdPart x = 
0 ↔ mk x != 0 where mpr h
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Hyperreal.archimedeanClassMk_omega_neg`：archimedeanClassMk_omega_neg : m
k ω < 0
-/
theorem stdPart_omega : stdPart ω = 0 := by
  rw [stdPart_eq_zero]
  exact archimedeanClassMk_omega_neg.ne

/-! #### ε -/

/-- A sample infinitesimal hyperreal ε = ⟦(0, 1, 1/2, 1/3, ⋯)⟧. -/
/-
**Hyperreal.epsilon** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：epsilon : Real*
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sample infinitesimal hyperreal ε = ⟦(0, 1, 1/2, 1/3, ⋯)⟧.
-/
def epsilon : ℝ* :=
  ofSeq fun n => n⁻¹

@[inherit_doc] scoped notation "ε" => Hyperreal.epsilon
recommended_spelling "epsilon" for "ε" in [epsilon, «termε»]

@[simp]
/-
**Hyperreal.inv_omega** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：inv_omega : ω⁻¹ = ε
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_omega : ω⁻¹ = ε :=
  rfl

@[simp]
/-
**Hyperreal.inv_epsilon** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：inv_epsilon : ε⁻¹ = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem inv_epsilon : ε⁻¹ = ω :=
  @inv_inv _ _ ω

@[simp]
/-
**Hyperreal.epsilon_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：epsilon_pos : 0 < ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Hyperreal.omega_pos`：omega_pos : 0 < ω
-/
theorem epsilon_pos : 0 < ε :=
  inv_pos_of_pos omega_pos

@[simp]
/-
**Hyperreal.epsilon_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：epsilon_ne_zero : ε != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Hyperreal.epsilon_pos`：epsilon_pos : 0 < ε
-/
theorem epsilon_ne_zero : ε ≠ 0 :=
  epsilon_pos.ne'

@[simp]
/-
**Hyperreal.epsilon_mul_omega** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：epsilon_mul_omega : ε * ω = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Hyperreal.omega_ne_zero`：omega_ne_zero : ω != 0
-/
theorem epsilon_mul_omega : ε * ω = 1 :=
  @inv_mul_cancel₀ _ _ ω omega_ne_zero

@[simp]
/-
**Hyperreal.archimedeanClassMk_epsilon_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`
。
形式化陈述：archimedeanClassMk_epsilon_pos : 0 < mk ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem archimedeanClassMk_epsilon_pos : 0 < mk ε := by
  simp [← inv_omega]

/-!
### Some facts about `Tendsto`
-/

@[simp]
/-
**Hyperreal.tendsto_ofSeq** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：tendsto_ofSeq {f : Nat -> Real} {lb : Filter Real} : (ofSeq f).Tendsto lb 
↔ Tendsto f (hyperfilter Nat) lb
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `instInfiniteNat`：Infinite ℕ

--- 原说明 ---
### Some facts about `Tendsto`
-/
theorem tendsto_ofSeq {f : ℕ → ℝ} {lb : Filter ℝ} :
    (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter ℕ) lb :=
  .rfl
/-
**Hyperreal.stdPart_map** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：stdPart_map {x : Real*} {r : Real} {f : Real -> Real} (hf : ContinuousAt f
 r) (hxr : x.Tendsto (𝓝 r)) : (x.map f).Tendsto (𝓝 (f r))
参数：hf : ContinuousAt f r；hxr : x.Tendsto (𝓝 r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem stdPart_map {x : ℝ*} {r : ℝ} {f : ℝ → ℝ} (hf : ContinuousAt f r)
    (hxr : x.Tendsto (𝓝 r)) : (x.map f).Tendsto (𝓝 (f r)) := by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact hf.tendsto.comp hxr
/-
**Hyperreal.stdPart_map** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：stdPart_map {x : Real*} {r : Real} {f : Real -> Real} (hf : ContinuousAt f
 r) (hxr : x.Tendsto (𝓝 r)) : (x.map f).Tendsto (𝓝 (f r))
参数：hf : ContinuousAt f r；hxr : x.Tendsto (𝓝 r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem stdPart_map₂ {x y : ℝ*} {r s : ℝ} {f : ℝ → ℝ → ℝ}
    (hxr : x.Tendsto (𝓝 r)) (hys : y.Tendsto (𝓝 s))
    (hf : ContinuousAt (Function.uncurry f) (r, s)) : (x.map₂ f y).Tendsto (𝓝 (f r s)) := by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  exact hf.tendsto.comp (hxr.prodMk_nhds hys)
/-
**Hyperreal.tendsto_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：tendsto_iff_forall {x : Real*} {r : Real} : x.Tendsto (𝓝 r) ↔ (forall s < 
r, s <= x) ∧ (forall s > r, x <= s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.tendsto_ofSeq`：tendsto_ofSeq {f : Nat -> Real} {lb : Filter Re
al} : (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter Nat) lb
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `nhds_basis_Ioo`：nhds_basis_Ioo [NoMaxOrder α] [NoMinOrder α] (a : α) : (
𝓝 a).HasBasis (fun b : α × α => b.1 < a ∧ a < b.2) fun b => Ioo b.1 b.2
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.coe_lt_coe`：coe_lt_coe {x y : Real} : (x : Real*) < y ↔ x < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem tendsto_iff_forall {x : ℝ*} {r : ℝ} :
    x.Tendsto (𝓝 r) ↔ (∀ s < r, s ≤ x) ∧ (∀ s > r, x ≤ s) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq, (nhds_basis_Ioo _).tendsto_right_iff]
  simp_rw [Set.mem_Ioo, eventually_and, ← ofSeq_lt_ofSeq]
  refine ⟨fun H ↦ ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩, fun H ⟨s, t⟩ ⟨hs, ht⟩ ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := exists_gt r
    exact (H ⟨s, t⟩ ⟨hs, ht⟩).1.le
  · obtain ⟨t, ht⟩ := exists_lt r
    exact (H ⟨t, s⟩ ⟨ht, hs⟩).2.le
  · obtain ⟨u, hu, hu'⟩ := exists_between hs
    exact (coe_lt_coe.2 hu).trans_le (H.1 _ hu')
  · obtain ⟨u, hu, hu'⟩ := exists_between ht
    exact (H.2 _ hu).trans_lt (coe_lt_coe.2 hu')
/-
**Hyperreal.archimedeanClassMk_nonneg_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Hype
rreal`。
形式化陈述：archimedeanClassMk_nonneg_of_tendsto {x : Real*} {r : Real} (hx : x.Tendst
o (𝓝 r)) : 0 <= mk x
参数：hx : x.Tendsto (𝓝 r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean`：mk_nonneg_of_le_o
f_le_of_archimedean [Archimedean S] (f : S ->+*o R) {x : R} {r s : S} (hr : f r 
<= x) (hs : x <= f s) : 0 <= mk x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.tendsto_iff_forall`：tendsto_iff_forall {x : Real*} {r : Real} 
: x.Tendsto (𝓝 r) ↔ (forall s < r, s <= x) ∧ (forall s > r, x <= s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem archimedeanClassMk_nonneg_of_tendsto {x : ℝ*} {r : ℝ} (hx : x.Tendsto (𝓝 r)) :
    0 ≤ mk x := by
  rw [tendsto_iff_forall] at hx
  obtain ⟨s, hs⟩ := exists_lt r
  obtain ⟨t, ht⟩ := exists_gt r
  exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom (hx.1 s hs) (hx.2 t ht)
/-
**Hyperreal.stdPart_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：stdPart_of_tendsto {x : Real*} {r : Real} (hx : x.Tendsto (𝓝 r)) : stdPart
 x = r
参数：hx : x.Tendsto (𝓝 r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `ArchimedeanClass.stdPart_eq`：stdPart_eq (f : Real ->+*o K) {r : Real} (h
l : forall s < r, f s <= x) (hr : forall s > r, x <= f s) : stdPart x = r
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.tendsto_iff_forall`：tendsto_iff_forall {x : Real*} {r : Real} 
: x.Tendsto (𝓝 r) ↔ (forall s < r, s <= x) ∧ (forall s > r, x <= s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem stdPart_of_tendsto {x : ℝ*} {r : ℝ} (hx : x.Tendsto (𝓝 r)) : stdPart x = r := by
  rw [tendsto_iff_forall] at hx
  exact stdPart_eq coeRingHom hx.1 hx.2
/-
**Hyperreal.archimedeanClassMk_pos_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Hyperre
al`。
形式化陈述：archimedeanClassMk_pos_of_tendsto {x : Real*} (hx : x.Tendsto (𝓝 0)) : 0 <
 mk x
参数：hx : x.Tendsto (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Hyperreal.archimedeanClassMk_nonneg_of_tendsto`：archimedeanClassMk_nonne
g_of_tendsto {x : Real*} {r : Real} (hx : x.Tendsto (𝓝 r)) : 0 <= mk x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.stdPart_eq_zero`：stdPart_eq_zero {x : K} : stdPart x = 
0 ↔ mk x != 0 where mpr h
· 使用定理 `Hyperreal.stdPart_of_tendsto`：stdPart_of_tendsto {x : Real*} {r : Real} 
(hx : x.Tendsto (𝓝 r)) : stdPart x = r
-/
theorem archimedeanClassMk_pos_of_tendsto {x : ℝ*} (hx : x.Tendsto (𝓝 0)) : 0 < mk x := by
  apply (archimedeanClassMk_nonneg_of_tendsto hx).lt_of_ne'
  rw [← stdPart_eq_zero, stdPart_of_tendsto hx]

@[simp]
/-
**Hyperreal.stdPart_epsilon** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：stdPart_epsilon : stdPart ε = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ArchimedeanClass.stdPart_eq_zero`：stdPart_eq_zero {x : K} : stdPart x = 
0 ↔ mk x != 0 where mpr h
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Hyperreal.archimedeanClassMk_epsilon_pos`：archimedeanClassMk_epsilon_pos
 : 0 < mk ε
-/
theorem stdPart_epsilon : stdPart ε = 0 :=
  stdPart_eq_zero.2 <| archimedeanClassMk_epsilon_pos.ne'
/-
**Hyperreal.epsilon_lt_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：epsilon_lt_of_pos {r : Real} : 0 < r -> ε < r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.lt_of_pos_of_archimedean`：lt_of_pos_of_archimedean [Arc
himedean S] (f : S ->+*o R) {x : R} (hx : 0 < mk x) {y : S} (hy : 0 < y) : x < f
 y
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Hyperreal.archimedeanClassMk_epsilon_pos`：archimedeanClassMk_epsilon_pos
 : 0 < mk ε
-/
theorem epsilon_lt_of_pos {r : ℝ} : 0 < r → ε < r :=
  lt_of_pos_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos
/-
**Hyperreal.epsilon_lt_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：epsilon_lt_of_neg {r : Real} : r < 0 -> r < ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.lt_of_neg_of_archimedean`：lt_of_neg_of_archimedean [Arc
himedean S] (f : S ->+*o R) {x : R} (hx : 0 < mk x) {y : S} (hy : y < 0) : f y <
 x
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Hyperreal.archimedeanClassMk_epsilon_pos`：archimedeanClassMk_epsilon_pos
 : 0 < mk ε
-/
theorem epsilon_lt_of_neg {r : ℝ} : r < 0 → r < ε :=
  lt_of_neg_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

@[deprecated (since := "2026-01-05")]
alias epsilon_lt_pos := epsilon_lt_of_pos

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
/-
**Hyperreal.lt_of_tendsto_zero_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：lt_of_tendsto_zero_of_pos {f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0)) :
 forall {r : Real}, 0 < r -> ofSeq f < (r : Real*)
参数：hf : Tendsto f atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_lt_ofSeq`：ofSeq_lt_ofSeq {f g : Nat -> Real} : ofSeq f <
 ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n < g n
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Nat.hyperfilter_le_atTop`：↑(Filter.hyperfilter ℕ) ≤ Filter.atTop
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → ofSeq f < (r : ℝ*) := fun hr ↦
  ofSeq_lt_ofSeq.2 <| (hf.eventually <| gt_mem_nhds hr).filter_mono Nat.hyperfilter_le_atTop

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
/-
**Hyperreal.neg_lt_of_tendsto_zero_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：neg_lt_of_tendsto_zero_of_pos {f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0
)) : forall {r : Real}, 0 < r -> (-r : Real*) < ofSeq f
参数：hf : Tendsto f atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `neg_lt_of_neg_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < b → -b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Hyperreal.lt_of_tendsto_zero_of_pos`：lt_of_tendsto_zero_of_pos {f : Nat 
-> Real} (hf : Tendsto f atTop (𝓝 0)) : forall {r : Real}, 0 < r -> ofSeq f < (r
 : Real*)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem neg_lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → (-r : ℝ*) < ofSeq f := fun hr =>
  have hg := hf.neg
  neg_lt_of_neg_lt (by rw [neg_zero] at hg; exact lt_of_tendsto_zero_of_pos hg hr)

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
/-
**Hyperreal.gt_of_tendsto_zero_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：gt_of_tendsto_zero_of_neg {f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0)) :
 forall {r : Real}, r < 0 -> (r : Real*) < ofSeq f
参数：hf : Tendsto f atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Hyperreal.coe_neg`：coe_neg (x : Real) : ↑(-x) = (-x : Real*)
· 使用定理 `Hyperreal.neg_lt_of_tendsto_zero_of_pos`：neg_lt_of_tendsto_zero_of_pos {
f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0)) : forall {r : Real}, 0 < r -> (-r 
: Real*) < ofSeq f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, r < 0 → (r : ℝ*) < ofSeq f := fun {r} hr => by
  rw [← neg_neg r, coe_neg]; exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)
/-
**Hyperreal.lt_of_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：lt_of_tendsto_atTop {x : Real*} (r : Real) (hx : x.Tendsto atTop) : r < x
参数：r : Real；hx : x.Tendsto atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.ofSeq_lt_ofSeq`：ofSeq_lt_ofSeq {f g : Nat -> Real} : ofSeq f <
 ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n < g n
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.tendsto_ofSeq`：tendsto_ofSeq {f : Nat -> Real} {lb : Filter Re
al} : (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter Nat) lb
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
theorem lt_of_tendsto_atTop {x : ℝ*} (r : ℝ) (hx : x.Tendsto atTop) : r < x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
  exact ofSeq_lt_ofSeq.2 <| hx.eventually_mem (Ioi_mem_atTop r)
/-
**Hyperreal.lt_of_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：lt_of_tendsto_atBot {x : Real*} (r : Real) (hx : x.Tendsto atBot) : x < r
参数：r : Real；hx : x.Tendsto atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.ofSeq_lt_ofSeq`：ofSeq_lt_ofSeq {f g : Nat -> Real} : ofSeq f <
 ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n < g n
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.tendsto_ofSeq`：tendsto_ofSeq {f : Nat -> Real} {lb : Filter Re
al} : (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter Nat) lb
· 使用定理 `Filter.Iio_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] [NoBotOrder α
] (x : α), Set.Iio x ∈ Filter.atBot
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
-/
theorem lt_of_tendsto_atBot {x : ℝ*} (r : ℝ) (hx : x.Tendsto atBot) : x < r := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
  exact ofSeq_lt_ofSeq.2 <| hx.eventually_mem (Iio_mem_atBot r)
/-
**Hyperreal.archimedeanClassMk_neg_of_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `H
yperreal`。
形式化陈述：archimedeanClassMk_neg_of_tendsto_atTop {x : Real*} (hx : x.Tendsto atTop)
 : mk x < 0
参数：hx : x.Tendsto atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.lt_of_tendsto_atTop`：lt_of_tendsto_atTop {x : Real*} (r : Real
) (hx : x.Tendsto atTop) : r < x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
theorem archimedeanClassMk_neg_of_tendsto_atTop {x : ℝ*} (hx : x.Tendsto atTop) : mk x < 0 := by
  have : 0 < x := lt_of_tendsto_atTop 0 hx
  intro n
  simpa [abs_of_pos this] using! lt_of_tendsto_atTop n hx
/-
**Hyperreal.archimedeanClassMk_neg_of_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `H
yperreal`。
形式化陈述：archimedeanClassMk_neg_of_tendsto_atBot {x : Real*} (hx : x.Tendsto atBot)
 : mk x < 0
参数：hx : x.Tendsto atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.lt_of_tendsto_atBot`：lt_of_tendsto_atBot {x : Real*} (r : Real
) (hx : x.Tendsto atBot) : x < r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem archimedeanClassMk_neg_of_tendsto_atBot {x : ℝ*} (hx : x.Tendsto atBot) : mk x < 0 := by
  have : x < 0 := lt_of_tendsto_atBot 0 hx
  intro n
  simpa [abs_of_neg this, lt_neg] using! lt_of_tendsto_atBot (-n) hx
/-
**Hyperreal.tendsto_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：tendsto_atTop_iff {x : Real*} : x.Tendsto atTop ↔ 0 < x ∧ mk x < 0 where m
p h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Hyperreal.lt_of_tendsto_atTop`：lt_of_tendsto_atTop {x : Real*} (r : Real
) (hx : x.Tendsto atTop) : r < x
· 使用定理 `Hyperreal.archimedeanClassMk_neg_of_tendsto_atTop`：archimedeanClassMk_ne
g_of_tendsto_atTop {x : Real*} (hx : x.Tendsto atTop) : mk x < 0
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.tendsto_ofSeq`：tendsto_ofSeq {f : Nat -> Real} {lb : Filter Re
al} : (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter Nat) lb
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Hyperreal.ofSeq_le_ofSeq`：ofSeq_le_ofSeq {f g : Nat -> Real} : ofSeq f <
= ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n <= g n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg`：∀ {M : Type u_1} [inst : AddC
ommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M}, 
  ArchimedeanClass.mk a < Archi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Hyperreal.archimedeanClassMk_coe_nonneg`：archimedeanClassMk_coe_nonneg (
x : Real) : 0 <= mk (x : Real*)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem tendsto_atTop_iff {x : ℝ*} : x.Tendsto atTop ↔ 0 < x ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atTop 0 h, archimedeanClassMk_neg_of_tendsto_atTop h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq, tendsto_atTop]
    exact fun r ↦ ofSeq_le_ofSeq.1 <|
      (lt_of_mk_lt_mk_of_nonneg (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le
/-
**Hyperreal.tendsto_atBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：tendsto_atBot_iff {x : Real*} : x.Tendsto atBot ↔ x < 0 ∧ mk x < 0 where m
p h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Hyperreal.lt_of_tendsto_atBot`：lt_of_tendsto_atBot {x : Real*} (r : Real
) (hx : x.Tendsto atBot) : x < r
· 使用定理 `Hyperreal.archimedeanClassMk_neg_of_tendsto_atBot`：archimedeanClassMk_ne
g_of_tendsto_atBot {x : Real*} (hx : x.Tendsto atBot) : mk x < 0
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.tendsto_ofSeq`：tendsto_ofSeq {f : Nat -> Real} {lb : Filter Re
al} : (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter Nat) lb
· 使用定理 `Filter.tendsto_atBot`：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β
] {m : α → β} {f : Filter α},   Filter.Tendsto m f Filter.atBot ↔ ∀ (b : β), ∀ᶠ 
(a : α) in…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Hyperreal.ofSeq_le_ofSeq`：ofSeq_le_ofSeq {f g : Nat -> Real} : ofSeq f <
= ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n <= g n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ArchimedeanClass.lt_of_mk_lt_mk_of_nonpos`：∀ {M : Type u_1} [inst : AddC
ommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M}, 
  ArchimedeanClass.mk a < Archi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Hyperreal.archimedeanClassMk_coe_nonneg`：archimedeanClassMk_coe_nonneg (
x : Real) : 0 <= mk (x : Real*)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem tendsto_atBot_iff {x : ℝ*} : x.Tendsto atBot ↔ x < 0 ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atBot 0 h, archimedeanClassMk_neg_of_tendsto_atBot h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq, tendsto_atBot]
    exact fun r ↦ ofSeq_le_ofSeq.1 <|
      (lt_of_mk_lt_mk_of_nonpos (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

/-- Standard part predicate.
**Do not use.** This is equivalent to the conjunction of `0 ≤ ArchimedeanClass.mk x` and
`ArchimedeanClass.stdPart x = r`. -/
@[deprecated stdPart (since := "2026-01-05")]
/-
**Hyperreal.IsSt** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：IsSt (x : Real*) (r : Real)
参数：x : Real*；r : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Standard part predicate.
**Do not use.** This is equivalent to the conjunction of `0 ≤ ArchimedeanClass.m
k x` and
`ArchimedeanClass.stdPart x = r`.
-/
def IsSt (x : ℝ*) (r : ℝ) :=
  ∀ δ : ℝ, 0 < δ → (r - δ : ℝ*) < x ∧ x < r + δ

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_iff {x r} : IsSt x r ↔ 0 <= mk x ∧ stdPart x = r where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean`：mk_nonneg_of_le_o
f_le_of_archimedean [Archimedean S] (f : S ->+*o R) {x : R} {r s : S} (hr : f r 
<= x) (hs : x <= f s) : 0 <= mk x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ArchimedeanClass.stdPart_eq`：stdPart_eq (f : Real ->+*o K) {r : Real} (h
l : forall s < r, f s <= x) (hr : forall s > r, x <= f s) : stdPart x = r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.coeRingHom_toFun`：∀ (x : ℝ), Hyperreal.coeRingHom x = ↑x
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `sub_pos_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, b < a → 0 < a - b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `ArchimedeanClass.lt_of_lt_stdPart`：lt_of_lt_stdPart (f : Real ->+*o K) {
r : Real} (hx : 0 <= mk x) (h : r < stdPart x) : f r < x
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `ArchimedeanClass.lt_of_stdPart_lt`：lt_of_stdPart_lt (f : Real ->+*o K) {
r : Real} (hx : 0 <= mk x) (h : stdPart x < r) : x < f r
-/
theorem isSt_iff {x r} : IsSt x r ↔ 0 ≤ mk x ∧ stdPart x = r where
  mp h := by
    refine ⟨?_, stdPart_eq coeRingHom (fun s hs ↦ ?_) (fun s hs ↦ ?_)⟩
    · have h := h 1 zero_lt_one
      exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom h.1.le h.2.le
    · simpa using (h _ (sub_pos_of_lt hs)).1.le
    · simpa using (h _ (sub_pos_of_lt hs)).2.le
  mpr h := by
    obtain ⟨h, rfl⟩ := h
    refine fun y hy ↦ ⟨?_, ?_⟩
    · apply lt_of_lt_stdPart coeRingHom h; simpa
    · apply lt_of_stdPart_lt coeRingHom h; simpa

open scoped Classical in
/-- Standard part function: like a "round" to ℝ instead of ℤ -/
@[deprecated stdPart (since := "2026-01-05")]
/-
**Hyperreal.st** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：st : Real* -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Standard part function: like a "round" to ℝ instead of ℤ
-/
noncomputable def st : ℝ* → ℝ := fun x => if h : ∃ r, IsSt x r then Classical.choose h else 0

@[deprecated "`st` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.st_eq** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：st_eq (x : Real*) : st x = stdPart x
参数：x : Real*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.st.eq_1`：∀ (x : ℝ*), x.st = if h : ∃ r, x.IsSt r then Classica
l.choose h else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Hyperreal.isSt_iff`：isSt_iff {x r} : IsSt x r ↔ 0 <= mk x ∧ stdPart x = 
r where mp h
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ArchimedeanClass.stdPart_eq_zero`：stdPart_eq_zero {x : K} : stdPart x = 
0 ↔ mk x != 0 where mpr h
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem st_eq (x : ℝ*) : st x = stdPart x := by
  rw [st]
  split_ifs with h
  · exact (isSt_iff.1 (Classical.choose_spec h)).2.symm
  · simp_rw [isSt_iff] at h
    push Not at h
    rw [eq_comm, stdPart_eq_zero]
    apply ne_of_lt
    by_contra! hx
    exact h _ hx rfl

/-- A hyperreal number is infinitesimal if its standard part is 0.
**Do not use.** Write `0 < ArchimedeanClass.mk x` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
/-
**Hyperreal.Infinitesimal** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：Infinitesimal (x : Real*)
参数：x : Real*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A hyperreal number is infinitesimal if its standard part is 0.
**Do not use.** Write `0 < ArchimedeanClass.mk x` instead.
-/
def Infinitesimal (x : ℝ*) :=
  IsSt x 0

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitesimal_iff {x : Real*} : Infinitesimal x ↔ 0 < mk x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.Infinitesimal.eq_1`：∀ (x : ℝ*), x.Infinitesimal = x.IsSt 0
· 使用定理 `Hyperreal.isSt_iff`：isSt_iff {x r} : IsSt x r ↔ 0 <= mk x ∧ stdPart x = 
r where mp h
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ArchimedeanClass.stdPart_eq_zero`：stdPart_eq_zero {x : K} : stdPart x = 
0 ↔ mk x != 0 where mpr h
· 使用定理 `lt_iff_le_and_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b
 < a ↔ b ≤ a ∧ a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infinitesimal_iff {x : ℝ*} : Infinitesimal x ↔ 0 < mk x := by
  rw [Infinitesimal, isSt_iff, stdPart_eq_zero, lt_iff_le_and_ne']

/-- A hyperreal number is positive infinite if it is larger than all real numbers.
**Do not use.** Write `0 < x ∧ ArchimedeanClass.mk x < 0` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
/-
**Hyperreal.InfinitePos** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：InfinitePos (x : Real*)
参数：x : Real*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A hyperreal number is positive infinite if it is larger than all real numbers.
**Do not use.** Write `0 < x ∧ ArchimedeanClass.mk x < 0` instead.
-/
def InfinitePos (x : ℝ*) :=
  ∀ r : ℝ, ↑r < x

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_iff {x : Real*} : InfinitePos x ↔ 0 < x ∧ mk x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg`：∀ {M : Type u_1} [inst : AddC
ommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M}, 
  ArchimedeanClass.mk a < Archi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ArchimedeanClass.mk_map_nonneg_of_archimedean`：mk_map_nonneg_of_archimed
ean [Archimedean S] (f : S ->+*o R) (y : S) : 0 <= mk (f y)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem infinitePos_iff {x : ℝ*} : InfinitePos x ↔ 0 < x ∧ mk x < 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hx, hx'⟩ r ↦ ?_⟩
  · have hx : 0 < x := h 0
    refine ⟨h 0, fun n ↦ ?_⟩
    simpa [abs_of_pos hx] using! h n
  · exact lt_of_mk_lt_mk_of_nonneg (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

/-- A hyperreal number is negative infinite if it is smaller than all real numbers.
**Do not use.** Write `x < 0 ∧ ArchimedeanClass.mk x < 0` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
/-
**Hyperreal.InfiniteNeg** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：InfiniteNeg (x : Real*)
参数：x : Real*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A hyperreal number is negative infinite if it is smaller than all real numbers.
**Do not use.** Write `x < 0 ∧ ArchimedeanClass.mk x < 0` instead.
-/
def InfiniteNeg (x : ℝ*) :=
  ∀ r : ℝ, x < r

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_iff {x : Real*} : InfiniteNeg x ↔ x < 0 ∧ mk x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ArchimedeanClass.lt_of_mk_lt_mk_of_nonpos`：∀ {M : Type u_1} [inst : AddC
ommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M}, 
  ArchimedeanClass.mk a < Archi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ArchimedeanClass.mk_map_nonneg_of_archimedean`：mk_map_nonneg_of_archimed
ean [Archimedean S] (f : S ->+*o R) (y : S) : 0 <= mk (f y)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem infiniteNeg_iff {x : ℝ*} : InfiniteNeg x ↔ x < 0 ∧ mk x < 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hx, hx'⟩ r ↦ ?_⟩
  · have hx : x < 0 := h 0
    refine ⟨h 0, fun n ↦ ?_⟩
    simpa [abs_of_neg hx, lt_neg] using! h (-n)
  · exact lt_of_mk_lt_mk_of_nonpos (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

/-- A hyperreal number is infinite if it is infinite positive or infinite negative.
**Do not use.** Write `ArchimedeanClass.mk x < 0` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
/-
**Hyperreal.Infinite** 是 Mathlib 中的一个定义，位于命名空间 `Hyperreal`。
形式化陈述：Infinite (x : Real*)
参数：x : Real*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A hyperreal number is infinite if it is infinite positive or infinite negative.
**Do not use.** Write `ArchimedeanClass.mk x < 0` instead.
-/
def Infinite (x : ℝ*) :=
  InfinitePos x ∨ InfiniteNeg x

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinite_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinite_iff {x : Real*} : Infinite x ↔ mk x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.Infinite.eq_1`：∀ (x : ℝ*), x.Infinite = (x.InfinitePos ∨ x.Inf
initeNeg)
· 使用定理 `Hyperreal.infinitePos_iff`：infinitePos_iff {x : Real*} : InfinitePos x ↔
 0 < x ∧ mk x < 0
· 使用定理 `Hyperreal.infiniteNeg_iff`：infiniteNeg_iff {x : Real*} : InfiniteNeg x ↔
 x < 0 ∧ mk x < 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
theorem infinite_iff {x : ℝ*} : Infinite x ↔ mk x < 0 := by
  rw [Infinite, infinitePos_iff, infiniteNeg_iff]
  aesop

@[deprecated tendsto_iff_forall (since := "2026-01-05")]
/-
**Hyperreal.isSt_ofSeq_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_ofSeq_iff_tendsto {f : Nat -> Real} {r : Real} : IsSt (ofSeq f) r ↔ T
endsto f (hyperfilter Nat) (𝓝 r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Hyperreal.ofSeq_lt_ofSeq`：ofSeq_lt_ofSeq {f g : Nat -> Real} : ofSeq f <
 ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n < g n
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.eventually_and`：eventually_and {p q : α -> Prop} {f : Filter α} :
 (forallᶠ x in f, p x ∧ q x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in f, q x
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `nhds_basis_Ioo_pos`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1
 : AddCommGroup α] [inst_2 : LinearOrder α] [IsOrderedAddMonoid α]   [OrderTopol
ogy α] […
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
theorem isSt_ofSeq_iff_tendsto {f : ℕ → ℝ} {r : ℝ} :
    IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter ℕ) (𝓝 r) :=
  Iff.trans (forall₂_congr fun _ _ ↦ (ofSeq_lt_ofSeq.and ofSeq_lt_ofSeq).trans eventually_and.symm)
    (nhds_basis_Ioo_pos _).tendsto_right_iff.symm

@[deprecated tendsto_iff_forall (since := "2026-01-05")]
/-
**Hyperreal.isSt_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_iff_tendsto {x : Real*} {r : Real} : IsSt x r ↔ x.Tendsto (𝓝 r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `Hyperreal.isSt_ofSeq_iff_tendsto`：isSt_ofSeq_iff_tendsto {f : Nat -> Rea
l} {r : Real} : IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter Nat) (𝓝 r)
-/
theorem isSt_iff_tendsto {x : ℝ*} {r : ℝ} : IsSt x r ↔ x.Tendsto (𝓝 r) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  exact isSt_ofSeq_iff_tendsto

@[deprecated stdPart_of_tendsto (since := "2026-01-05")]
/-
**Hyperreal.isSt_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_of_tendsto {f : Nat -> Real} {r : Real} (hf : Tendsto f atTop (𝓝 r)) 
: IsSt (ofSeq f) r
参数：hf : Tendsto f atTop (𝓝 r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.isSt_ofSeq_iff_tendsto`：isSt_ofSeq_iff_tendsto {f : Nat -> Rea
l} {r : Real} : IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter Nat) (𝓝 r)
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Nat.hyperfilter_le_atTop`：↑(Filter.hyperfilter ℕ) ≤ Filter.atTop
-/
theorem isSt_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : Tendsto f atTop (𝓝 r)) : IsSt (ofSeq f) r :=
  isSt_ofSeq_iff_tendsto.2 <| hf.mono_left Nat.hyperfilter_le_atTop

@[deprecated "Use `stdPart_monotoneOn` and `MonotoneOn.reflect_lt`" (since := "2026-01-05")]
/-
**Hyperreal.IsSt.lt** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → r < s → x < y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_lt_ofSeq`：ofSeq_lt_ofSeq {f g : Nat -> Real} : ofSeq f <
 ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n < g n
· 使用定理 `Filter.Tendsto.eventually_lt`：Filter.Tendsto.eventually_lt {l : Filter γ
} {f g : γ -> α} {y z : α} (hf : Tendsto f l (𝓝 y)) (hg : Tendsto g l (𝓝 z)) (hy
z : y < z) : foral…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.isSt_ofSeq_iff_tendsto`：isSt_ofSeq_iff_tendsto {f : Nat -> Rea
l} {r : Real} : IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter Nat) (𝓝 r)
-/
protected theorem IsSt.lt {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) (hrs : r < s) :
    x < y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
  exact ofSeq_lt_ofSeq.2 <| hxr.eventually_lt hys hrs

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.IsSt.unique** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x : ℝ*} {r s : ℝ}, x.IsSt r → x.IsSt s → r = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.isSt_ofSeq_iff_tendsto`：isSt_ofSeq_iff_tendsto {f : Nat -> Rea
l} {r : Real} : IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter Nat) (𝓝 r)
-/
theorem IsSt.unique {x : ℝ*} {r s : ℝ} (hr : IsSt x r) (hs : IsSt x s) : r = s := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hr hs
  exact tendsto_nhds_unique hr hs

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.IsSt.st_eq** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → x.st = r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.st.eq_1`：∀ (x : ℝ*), x.st = if h : ∃ r, x.IsSt r then Classica
l.choose h else 0
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Hyperreal.IsSt.unique`：∀ {x : ℝ*} {r s : ℝ}, x.IsSt r → x.IsSt s → r = s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem IsSt.st_eq {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : st x = r := by
  have h : ∃ r, IsSt x r := ⟨r, hxr⟩
  rw [st, dif_pos h]
  exact (Classical.choose_spec h).unique hxr

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.IsSt.not_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → ¬x.Infinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsSt.not_infinite {x : ℝ*} {r : ℝ} (h : IsSt x r) : ¬Infinite x := fun hi ↦
  hi.elim (fun hp ↦ lt_asymm (h 1 one_pos).2 (hp (r + 1))) fun hn ↦
    lt_asymm (h 1 one_pos).1 (hn (r - 1))

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.not_infinite_of_exists_st** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：not_infinite_of_exists_st {x : Real*} : (exists r : Real, IsSt x r) -> ¬In
finite x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.not_infinite`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → ¬x.Infinite
-/
theorem not_infinite_of_exists_st {x : ℝ*} : (∃ r : ℝ, IsSt x r) → ¬Infinite x := fun ⟨_r, hr⟩ =>
  hr.not_infinite

@[deprecated stdPart_eq_zero (since := "2026-01-05")]
/-
**Hyperreal.Infinite.st_eq** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.Infinite`。
形式化陈述：∀ {x : ℝ*}, x.Infinite → x.st = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Hyperreal.IsSt.not_infinite`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → ¬x.Infinite
-/
theorem Infinite.st_eq {x : ℝ*} (hi : Infinite x) : st x = 0 :=
  dif_neg fun ⟨_r, hr⟩ ↦ hr.not_infinite hi

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]
/-
**Hyperreal.isSt_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_sSup {x : Real*} (hni : ¬Infinite x) : IsSt x (sSup { y : Real | (y :
 Real*) < x })
参数：hni : ¬Infinite x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.isSt_iff`：isSt_iff {x r} : IsSt x r ↔ 0 <= mk x ∧ stdPart x = 
r where mp h
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Hyperreal.infinite_iff`：infinite_iff {x : Real*} : Infinite x ↔ mk x < 0
· 使用定理 `ArchimedeanClass.stdPart_eq_sSup`：stdPart_eq_sSup (f : Real ->+*o K) (x 
: K) : stdPart x = sSup {r | f r < x}
-/
theorem isSt_sSup {x : ℝ*} (hni : ¬Infinite x) : IsSt x (sSup { y : ℝ | (y : ℝ*) < x }) := by
  rw [infinite_iff, not_lt] at hni
  rw [isSt_iff]
  exact ⟨hni, stdPart_eq_sSup coeRingHom x⟩

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]
/-
**Hyperreal.exists_st_of_not_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：exists_st_of_not_infinite {x : Real*} (hni : ¬Infinite x) : exists r : Rea
l, IsSt x r
参数：hni : ¬Infinite x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.isSt_sSup`：isSt_sSup {x : Real*} (hni : ¬Infinite x) : IsSt x 
(sSup { y : Real | (y : Real*) < x })
-/
theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬Infinite x) : ∃ r : ℝ, IsSt x r :=
  ⟨sSup { y : ℝ | (y : ℝ*) < x }, isSt_sSup hni⟩

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]
/-
**Hyperreal.st_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：st_eq_sSup {x : Real*} : st x = sSup { y : Real | (y : Real*) < x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.st_eq`：st_eq (x : Real*) : st x = stdPart x
· 使用定理 `ArchimedeanClass.stdPart_eq_sSup`：stdPart_eq_sSup (f : Real ->+*o K) (x 
: K) : stdPart x = sSup {r | f r < x}
-/
theorem st_eq_sSup {x : ℝ*} : st x = sSup { y : ℝ | (y : ℝ*) < x } := by
  rw [st_eq]
  exact stdPart_eq_sSup coeRingHom x

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.exists_st_iff_not_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：exists_st_iff_not_infinite {x : Real*} : (exists r : Real, IsSt x r) ↔ ¬In
finite x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.not_infinite_of_exists_st`：not_infinite_of_exists_st {x : Real
*} : (exists r : Real, IsSt x r) -> ¬Infinite x
· 使用定理 `Hyperreal.exists_st_of_not_infinite`：exists_st_of_not_infinite {x : Real
*} (hni : ¬Infinite x) : exists r : Real, IsSt x r
-/
theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, IsSt x r) ↔ ¬Infinite x :=
  ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinite_iff_not_exists_st** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinite_iff_not_exists_st {x : Real*} : Infinite x ↔ ¬exists r : Real, Is
St x r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `Hyperreal.exists_st_iff_not_infinite`：exists_st_iff_not_infinite {x : Re
al*} : (exists r : Real, IsSt x r) ↔ ¬Infinite x
-/
theorem infinite_iff_not_exists_st {x : ℝ*} : Infinite x ↔ ¬∃ r : ℝ, IsSt x r :=
  iff_not_comm.mp exists_st_iff_not_infinite

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.IsSt.isSt_st** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → x.IsSt x.st
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.IsSt.st_eq`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → x.st = r
-/
theorem IsSt.isSt_st {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt x (st x) := by
  rwa [hxr.st_eq]

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_st_of_exists_st** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_st_of_exists_st {x : Real*} (hx : exists r : Real, IsSt x r) : IsSt x
 (st x)
参数：hx : exists r : Real, IsSt x r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.isSt_st`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → x.IsSt x.st
-/
theorem isSt_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, IsSt x r) : IsSt x (st x) :=
  let ⟨_r, hr⟩ := hx; hr.isSt_st

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_st'** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_st' {x : Real*} (hx : ¬Infinite x) : IsSt x (st x)
参数：hx : ¬Infinite x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.isSt_st`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → x.IsSt x.st
· 使用定理 `Hyperreal.isSt_sSup`：isSt_sSup {x : Real*} (hni : ¬Infinite x) : IsSt x 
(sSup { y : Real | (y : Real*) < x })
-/
theorem isSt_st' {x : ℝ*} (hx : ¬Infinite x) : IsSt x (st x) :=
  (isSt_sSup hx).isSt_st

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_st** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_st {x : Real*} (hx : st x != 0) : IsSt x (st x)
参数：hx : st x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.isSt_st'`：isSt_st' {x : Real*} (hx : ¬Infinite x) : IsSt x (st
 x)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Hyperreal.Infinite.st_eq`：∀ {x : ℝ*}, x.Infinite → x.st = 0
-/
theorem isSt_st {x : ℝ*} (hx : st x ≠ 0) : IsSt x (st x) :=
  isSt_st' <| mt Infinite.st_eq hx

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_refl_real** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_refl_real (r : Real) : IsSt r r
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.isSt_ofSeq_iff_tendsto`：isSt_ofSeq_iff_tendsto {f : Nat -> Rea
l} {r : Real} : IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter Nat) (𝓝 r)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem isSt_refl_real (r : ℝ) : IsSt r r := isSt_ofSeq_iff_tendsto.2 tendsto_const_nhds

@[deprecated stdPart_coe (since := "2026-01-05")]
/-
**Hyperreal.st_id_real** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：st_id_real (r : Real) : st r = r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.st_eq`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → x.st = r
· 使用定理 `Hyperreal.isSt_refl_real`：isSt_refl_real (r : Real) : IsSt r r
-/
theorem st_id_real (r : ℝ) : st r = r := (isSt_refl_real r).st_eq

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.eq_of_isSt_real** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：eq_of_isSt_real {r s : Real} : IsSt r s -> r = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.unique`：∀ {x : ℝ*} {r s : ℝ}, x.IsSt r → x.IsSt s → r = s
· 使用定理 `Hyperreal.isSt_refl_real`：isSt_refl_real (r : Real) : IsSt r r
-/
theorem eq_of_isSt_real {r s : ℝ} : IsSt r s → r = s :=
  (isSt_refl_real r).unique

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_real_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_real_iff_eq {r s : Real} : IsSt r s ↔ r = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.eq_of_isSt_real`：eq_of_isSt_real {r s : Real} : IsSt r s -> r 
= s
· 使用定理 `Hyperreal.isSt_refl_real`：isSt_refl_real (r : Real) : IsSt r r
-/
theorem isSt_real_iff_eq {r s : ℝ} : IsSt r s ↔ r = s :=
  ⟨eq_of_isSt_real, fun hrs => hrs ▸ isSt_refl_real r⟩

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_symm_real** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_symm_real {r s : Real} : IsSt r s ↔ IsSt s r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.isSt_real_iff_eq`：isSt_real_iff_eq {r s : Real} : IsSt r s ↔ r
 = s
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSt_symm_real {r s : ℝ} : IsSt r s ↔ IsSt s r := by
  rw [isSt_real_iff_eq, isSt_real_iff_eq, eq_comm]

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_trans_real** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_trans_real {r s t : Real} : IsSt r s -> IsSt s t -> IsSt r t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.isSt_real_iff_eq`：isSt_real_iff_eq {r s : Real} : IsSt r s ↔ r
 = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem isSt_trans_real {r s t : ℝ} : IsSt r s → IsSt s t → IsSt r t := by
  rw [isSt_real_iff_eq, isSt_real_iff_eq, isSt_real_iff_eq]; exact Eq.trans

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_inj_real** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_inj_real {r₁ r₂ s : Real} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s) : r₁ = r₂
参数：h1 : IsSt r₁ s；h2 : IsSt r₂ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Hyperreal.eq_of_isSt_real`：eq_of_isSt_real {r s : Real} : IsSt r s -> r 
= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isSt_inj_real {r₁ r₂ s : ℝ} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s) : r₁ = r₂ :=
  Eq.trans (eq_of_isSt_real h1) (eq_of_isSt_real h2).symm

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.isSt_iff_abs_sub_lt_delta** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：isSt_iff_abs_sub_lt_delta {x : Real*} {r : Real} : IsSt x r ↔ forall δ : R
eal, 0 < δ -> |x - ↑r| < δ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSt_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} : IsSt x r ↔ ∀ δ : ℝ, 0 < δ → |x - ↑r| < δ := by
  simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, IsSt, and_comm, add_comm]

@[deprecated stdPart_map (since := "2026-01-05")]
/-
**Hyperreal.IsSt.map** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → ∀ {f : ℝ → ℝ}, ContinuousAt f r → Hyperreal
.IsSt (Filter.Germ.map f x) (f r)
参数：Filter.Germ.map f x；f r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.isSt_ofSeq_iff_tendsto`：isSt_ofSeq_iff_tendsto {f : Nat -> Rea
l} {r : Real} : IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter Nat) (𝓝 r)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem IsSt.map {x : ℝ*} {r : ℝ} (hxr : IsSt x r) {f : ℝ → ℝ} (hf : ContinuousAt f r) :
    IsSt (x.map f) (f r) := by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact isSt_ofSeq_iff_tendsto.2 <| hf.tendsto.comp (isSt_ofSeq_iff_tendsto.1 hxr)

@[deprecated stdPart_map₂ (since := "2026-01-05")]
/-
**Hyperreal.IsSt.map** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → ∀ {f : ℝ → ℝ}, ContinuousAt f r → Hyperreal
.IsSt (Filter.Germ.map f x) (f r)
参数：Filter.Germ.map f x；f r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Hyperreal.ofSeq_surjective`：ofSeq_surjective : Function.Surjective ofSeq
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.isSt_ofSeq_iff_tendsto`：isSt_ofSeq_iff_tendsto {f : Nat -> Rea
l} {r : Real} : IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter Nat) (𝓝 r)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem IsSt.map₂ {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousAt (Function.uncurry f) (r, s)) : IsSt (x.map₂ f y) (f r s) := by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
  exact isSt_ofSeq_iff_tendsto.2 <| hf.tendsto.comp (hxr.prodMk_nhds hys)

@[deprecated stdPart_add (since := "2026-01-05")]
/-
**Hyperreal.IsSt.add** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → (x + y).IsSt (r + s)
参数：x + y；r + s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.map₂`：∀ {x y : ℝ*} {r s : ℝ},   x.IsSt r →     y.IsSt s →
       ∀ {f : ℝ → ℝ → ℝ}, ContinuousAt (Function.uncurry f) (r, s) → Hyperreal.I
sSt (Filt…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
theorem IsSt.add {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) :
    IsSt (x + y) (r + s) := hxr.map₂ hys continuous_add.continuousAt

@[deprecated stdPart_neg (since := "2026-01-05")]
/-
**Hyperreal.IsSt.neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → (-x).IsSt (-r)
参数：-x；-r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.map`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → ∀ {f : ℝ → ℝ}, Contin
uousAt f r → Hyperreal.IsSt (Filter.Germ.map f x) (f r)
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousNeg.continuous_neg`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Neg G} [self : ContinuousNeg G], Continuous fun a => -a
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
theorem IsSt.neg {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt (-x) (-r) :=
  hxr.map continuous_neg.continuousAt

@[deprecated stdPart_sub (since := "2026-01-05")]
/-
**Hyperreal.IsSt.sub** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → (x - y).IsSt (r - s)
参数：x - y；r - s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.map₂`：∀ {x y : ℝ*} {r s : ℝ},   x.IsSt r →     y.IsSt s →
       ∀ {f : ℝ → ℝ → ℝ}, ContinuousAt (Function.uncurry f) (r, s) → Hyperreal.I
sSt (Filt…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousSub.continuous_sub`：∀ {G : Type u_4} {inst : TopologicalSpace 
G} {inst_1 : Sub G} [self : ContinuousSub G], Continuous fun p => p.1 - p.2
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
-/
theorem IsSt.sub {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x - y) (r - s) :=
  hxr.map₂ hys continuous_sub.continuousAt

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
/-
**Hyperreal.IsSt.le** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → x ≤ y → r ≤ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Hyperreal.IsSt.lt`：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → r < s →
 x < y
-/
theorem IsSt.le {x y : ℝ*} {r s : ℝ} (hrx : IsSt x r) (hsy : IsSt y s) (hxy : x ≤ y) : r ≤ s :=
  not_lt.1 fun h ↦ hxy.not_gt <| hsy.lt hrx h

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
/-
**Hyperreal.st_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：st_le_of_le {x y : Real*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x <= y
 -> st x <= st y
参数：hix : ¬Infinite x；hiy : ¬Infinite y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.le`：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → x ≤ y →
 r ≤ s
· 使用定理 `Hyperreal.isSt_st'`：isSt_st' {x : Real*} (hx : ¬Infinite x) : IsSt x (st
 x)
-/
theorem st_le_of_le {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x ≤ y → st x ≤ st y :=
  (isSt_st' hix).le (isSt_st' hiy)

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
/-
**Hyperreal.lt_of_st_lt** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：lt_of_st_lt {x y : Real*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x <
 st y -> x < y
参数：hix : ¬Infinite x；hiy : ¬Infinite y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.lt`：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → r < s →
 x < y
· 使用定理 `Hyperreal.isSt_st'`：isSt_st' {x : Real*} (hx : ¬Infinite x) : IsSt x (st
 x)
-/
theorem lt_of_st_lt {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x < st y → x < y :=
  (isSt_st' hix).lt (isSt_st' hiy)

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_def** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_def {x : Real*} : InfinitePos x ↔ forall r : Real, ↑r < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infinitePos_def {x : ℝ*} : InfinitePos x ↔ ∀ r : ℝ, ↑r < x := Iff.rfl

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_def** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_def {x : Real*} : InfiniteNeg x ↔ forall r : Real, x < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infiniteNeg_def {x : ℝ*} : InfiniteNeg x ↔ ∀ r : ℝ, x < r := Iff.rfl

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.InfinitePos.pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.InfinitePos`。
形式化陈述：∀ {x : ℝ*}, x.InfinitePos → 0 < x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem InfinitePos.pos {x : ℝ*} (hip : InfinitePos x) : 0 < x := hip 0

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.InfiniteNeg.lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.InfiniteNeg
`。
形式化陈述：∀ {x : ℝ*}, x.InfiniteNeg → x < 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem InfiniteNeg.lt_zero {x : ℝ*} : InfiniteNeg x → x < 0 := fun hin => hin 0

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.Infinite.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.Infinite`。
形式化陈述：∀ {x : ℝ*}, x.Infinite → x ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Hyperreal.InfinitePos.pos`：∀ {x : ℝ*}, x.InfinitePos → 0 < x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Hyperreal.InfiniteNeg.lt_zero`：∀ {x : ℝ*}, x.InfiniteNeg → x < 0
-/
theorem Infinite.ne_zero {x : ℝ*} (hI : Infinite x) : x ≠ 0 :=
  hI.elim (fun hip => hip.pos.ne') fun hin => hin.lt_zero.ne

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.not_infinite_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：not_infinite_zero : ¬Infinite 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.Infinite.ne_zero`：∀ {x : ℝ*}, x.Infinite → x ≠ 0
-/
theorem not_infinite_zero : ¬Infinite 0 := fun hI => hI.ne_zero rfl

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.InfiniteNeg.not_infinitePos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.Inf
initeNeg`。
形式化陈述：∀ {x : ℝ*}, x.InfiniteNeg → ¬x.InfinitePos
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem InfiniteNeg.not_infinitePos {x : ℝ*} : InfiniteNeg x → ¬InfinitePos x := fun hn hp =>
  (hn 0).not_gt (hp 0)

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.InfinitePos.not_infiniteNeg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.Inf
initePos`。
形式化陈述：∀ {x : ℝ*}, x.InfinitePos → ¬x.InfiniteNeg
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.InfiniteNeg.not_infinitePos`：∀ {x : ℝ*}, x.InfiniteNeg → ¬x.In
finitePos
-/
theorem InfinitePos.not_infiniteNeg {x : ℝ*} (hp : InfinitePos x) : ¬InfiniteNeg x := fun hn ↦
  hn.not_infinitePos hp

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.InfinitePos.neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.InfinitePos`。
形式化陈述：∀ {x : ℝ*}, x.InfinitePos → (-x).InfiniteNeg
参数：-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   -a < b ↔ -b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem InfinitePos.neg {x : ℝ*} : InfinitePos x → InfiniteNeg (-x) := fun hp r =>
  neg_lt.mp (hp (-r))

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.InfiniteNeg.neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.InfiniteNeg`。
形式化陈述：∀ {x : ℝ*}, x.InfiniteNeg → (-x).InfinitePos
参数：-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   a < -b ↔ b < -a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem InfiniteNeg.neg {x : ℝ*} : InfiniteNeg x → InfinitePos (-x) := fun hp r =>
  lt_neg.mp (hp (-r))

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_neg {x : Real*} : InfiniteNeg (-x) ↔ InfinitePos x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.InfiniteNeg.neg`：∀ {x : ℝ*}, x.InfiniteNeg → (-x).InfinitePos
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Hyperreal.InfinitePos.neg`：∀ {x : ℝ*}, x.InfinitePos → (-x).InfiniteNeg
-/
theorem infiniteNeg_neg {x : ℝ*} : InfiniteNeg (-x) ↔ InfinitePos x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfinitePos.neg⟩

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_neg {x : Real*} : InfinitePos (-x) ↔ InfiniteNeg x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.InfinitePos.neg`：∀ {x : ℝ*}, x.InfinitePos → (-x).InfiniteNeg
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Hyperreal.InfiniteNeg.neg`：∀ {x : ℝ*}, x.InfiniteNeg → (-x).InfinitePos
-/
theorem infinitePos_neg {x : ℝ*} : InfinitePos (-x) ↔ InfiniteNeg x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfiniteNeg.neg⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinite_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinite_neg {x : Real*} : Infinite (-x) ↔ Infinite x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.or`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `Hyperreal.infiniteNeg_neg`：infiniteNeg_neg {x : Real*} : InfiniteNeg (-x
) ↔ InfinitePos x
· 使用定理 `Hyperreal.infinitePos_neg`：infinitePos_neg {x : Real*} : InfinitePos (-x
) ↔ InfiniteNeg x
-/
theorem infinite_neg {x : ℝ*} : Infinite (-x) ↔ Infinite x :=
  or_comm.trans <| infiniteNeg_neg.or infinitePos_neg

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.not_infinite {x : ℝ*} (h : Infinitesimal x) : ¬Infinite x :=
  h.not_infinite

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.Infinite.not_infinitesimal** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.Infi
nite`。
形式化陈述：∀ {x : ℝ*}, x.Infinite → ¬x.Infinitesimal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.Infinitesimal.not_infinite`：∀ {x : ℝ*}, x.Infinitesimal → ¬x.I
nfinite
-/
theorem Infinite.not_infinitesimal {x : ℝ*} (h : Infinite x) : ¬Infinitesimal x := fun h' ↦
  h'.not_infinite h

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.InfinitePos.not_infinitesimal** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.I
nfinitePos`。
形式化陈述：∀ {x : ℝ*}, x.InfinitePos → ¬x.Infinitesimal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.Infinite.not_infinitesimal`：∀ {x : ℝ*}, x.Infinite → ¬x.Infini
tesimal
-/
theorem InfinitePos.not_infinitesimal {x : ℝ*} (h : InfinitePos x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inl h)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.InfiniteNeg.not_infinitesimal** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.I
nfiniteNeg`。
形式化陈述：∀ {x : ℝ*}, x.InfiniteNeg → ¬x.Infinitesimal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.Infinite.not_infinitesimal`：∀ {x : ℝ*}, x.Infinite → ¬x.Infini
tesimal
-/
theorem InfiniteNeg.not_infinitesimal {x : ℝ*} (h : InfiniteNeg x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inr h)

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_iff_infinite_and_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperrea
l`。
形式化陈述：infinitePos_iff_infinite_and_pos {x : Real*} : InfinitePos x ↔ Infinite x 
∧ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem infinitePos_iff_infinite_and_pos {x : ℝ*} : InfinitePos x ↔ Infinite x ∧ 0 < x :=
  ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn id fun hin => False.elim (not_lt_of_gt hp (hin 0))⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_iff_infinite_and_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperrea
l`。
形式化陈述：infiniteNeg_iff_infinite_and_neg {x : Real*} : InfiniteNeg x ↔ Infinite x 
∧ x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem infiniteNeg_iff_infinite_and_neg {x : ℝ*} : InfiniteNeg x ↔ Infinite x ∧ x < 0 :=
  ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_gt hp (hin 0))) fun hip => hip⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_iff_infinite_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperr
eal`。
形式化陈述：infinitePos_iff_infinite_of_nonneg {x : Real*} (hp : 0 <= x) : InfinitePos
 x ↔ Infinite x
参数：hp : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Hyperreal.InfiniteNeg.lt_zero`：∀ {x : ℝ*}, x.InfiniteNeg → x < 0
-/
theorem infinitePos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : InfinitePos x ↔ Infinite x :=
  .symm <| or_iff_left fun h ↦ h.lt_zero.not_ge hp

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_iff_infinite_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal
`。
形式化陈述：infinitePos_iff_infinite_of_pos {x : Real*} (hp : 0 < x) : InfinitePos x ↔
 Infinite x
参数：hp : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitePos_iff_infinite_of_nonneg`：infinitePos_iff_infinite_o
f_nonneg {x : Real*} (hp : 0 <= x) : InfinitePos x ↔ Infinite x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem infinitePos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : InfinitePos x ↔ Infinite x :=
  infinitePos_iff_infinite_of_nonneg hp.le

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_iff_infinite_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal
`。
形式化陈述：infiniteNeg_iff_infinite_of_neg {x : Real*} (hn : x < 0) : InfiniteNeg x ↔
 Infinite x
参数：hn : x < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Hyperreal.InfinitePos.pos`：∀ {x : ℝ*}, x.InfinitePos → 0 < x
-/
theorem infiniteNeg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : InfiniteNeg x ↔ Infinite x :=
  .symm <| or_iff_right fun h ↦ h.pos.not_gt hn

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_abs_iff_infinite_abs** 是 Mathlib 中的一个定理，位于命名空间 `Hyperrea
l`。
形式化陈述：infinitePos_abs_iff_infinite_abs {x : Real*} : InfinitePos |x| ↔ Infinite 
|x|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitePos_iff_infinite_of_nonneg`：infinitePos_iff_infinite_o
f_nonneg {x : Real*} (hp : 0 <= x) : InfinitePos x ↔ Infinite x
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem infinitePos_abs_iff_infinite_abs {x : ℝ*} : InfinitePos |x| ↔ Infinite |x| :=
  infinitePos_iff_infinite_of_nonneg (abs_nonneg _)

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinite_abs_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinite_abs_iff {x : Real*} : Infinite |x| ↔ Infinite x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
-/
theorem infinite_abs_iff {x : ℝ*} : Infinite |x| ↔ Infinite x := by
  cases le_total 0 x <;> simp [*, abs_of_nonneg, abs_of_nonpos, infinite_neg]

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_abs_iff_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_abs_iff_infinite {x : Real*} : InfinitePos |x| ↔ Infinite x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Hyperreal.infinitePos_abs_iff_infinite_abs`：infinitePos_abs_iff_infinite
_abs {x : Real*} : InfinitePos |x| ↔ Infinite |x|
· 使用定理 `Hyperreal.infinite_abs_iff`：infinite_abs_iff {x : Real*} : Infinite |x| 
↔ Infinite x
-/
theorem infinitePos_abs_iff_infinite {x : ℝ*} : InfinitePos |x| ↔ Infinite x :=
  infinitePos_abs_iff_infinite_abs.trans infinite_abs_iff

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinite_iff_abs_lt_abs** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinite_iff_abs_lt_abs {x : Real*} : Infinite x ↔ forall r : Real, (|r| :
 Real*) < |x|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Hyperreal.infinitePos_abs_iff_infinite`：infinitePos_abs_iff_infinite {x 
: Real*} : InfinitePos |x| ↔ Infinite x
· 使用定理 `Hyperreal.coe_abs`：coe_abs (x : Real) : ((|x| : Real) : Real*) = |↑x|
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem infinite_iff_abs_lt_abs {x : ℝ*} : Infinite x ↔ ∀ r : ℝ, (|r| : ℝ*) < |x| :=
  infinitePos_abs_iff_infinite.symm.trans ⟨fun hI r => coe_abs r ▸ hI |r|, fun hR r =>
    (le_abs_self _).trans_lt (hR r)⟩

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_add_not_infiniteNeg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal
`。
形式化陈述：infinitePos_add_not_infiniteNeg {x y : Real*} : InfinitePos x -> ¬Infinite
Neg y -> InfinitePos (x + y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem infinitePos_add_not_infiniteNeg {x y : ℝ*} :
    InfinitePos x → ¬InfiniteNeg y → InfinitePos (x + y) := by
  intro hip hnin r
  obtain ⟨r₂, hr₂⟩ := not_forall.mp hnin
  convert! add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.not_infiniteNeg_add_infinitePos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal
`。
形式化陈述：not_infiniteNeg_add_infinitePos {x y : Real*} : ¬InfiniteNeg x -> Infinite
Pos y -> InfinitePos (x + y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitePos_add_not_infiniteNeg`：infinitePos_add_not_infiniteN
eg {x y : Real*} : InfinitePos x -> ¬InfiniteNeg y -> InfinitePos (x + y)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem not_infiniteNeg_add_infinitePos {x y : ℝ*} :
    ¬InfiniteNeg x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  add_comm y x ▸ infinitePos_add_not_infiniteNeg hy hx

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_add_not_infinitePos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal
`。
形式化陈述：infiniteNeg_add_not_infinitePos {x y : Real*} : InfiniteNeg x -> ¬Infinite
Pos y -> InfiniteNeg (x + y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Hyperreal.infinitePos_neg`：infinitePos_neg {x : Real*} : InfinitePos (-x
) ↔ InfiniteNeg x
· 使用定理 `Hyperreal.infiniteNeg_neg`：infiniteNeg_neg {x : Real*} : InfiniteNeg (-x
) ↔ InfinitePos x
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Hyperreal.infinitePos_add_not_infiniteNeg`：infinitePos_add_not_infiniteN
eg {x y : Real*} : InfinitePos x -> ¬InfiniteNeg y -> InfinitePos (x + y)
-/
theorem infiniteNeg_add_not_infinitePos {x y : ℝ*} :
    InfiniteNeg x → ¬InfinitePos y → InfiniteNeg (x + y) := by
  rw [← infinitePos_neg, ← infinitePos_neg, ← @infiniteNeg_neg y, neg_add]
  exact infinitePos_add_not_infiniteNeg

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.not_infinitePos_add_infiniteNeg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal
`。
形式化陈述：not_infinitePos_add_infiniteNeg {x y : Real*} : ¬InfinitePos x -> Infinite
Neg y -> InfiniteNeg (x + y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infiniteNeg_add_not_infinitePos`：infiniteNeg_add_not_infiniteP
os {x y : Real*} : InfiniteNeg x -> ¬InfinitePos y -> InfiniteNeg (x + y)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem not_infinitePos_add_infiniteNeg {x y : ℝ*} :
    ¬InfinitePos x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  add_comm y x ▸ infiniteNeg_add_not_infinitePos hy hx

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_add_infinitePos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_add_infinitePos {x y : Real*} : InfinitePos x -> InfinitePos y
 -> InfinitePos (x + y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitePos_add_not_infiniteNeg`：infinitePos_add_not_infiniteN
eg {x y : Real*} : InfinitePos x -> ¬InfiniteNeg y -> InfinitePos (x + y)
· 使用定理 `Hyperreal.InfinitePos.not_infiniteNeg`：∀ {x : ℝ*}, x.InfinitePos → ¬x.In
finiteNeg
-/
theorem infinitePos_add_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx hy.not_infiniteNeg

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_add_infiniteNeg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_add_infiniteNeg {x y : Real*} : InfiniteNeg x -> InfiniteNeg y
 -> InfiniteNeg (x + y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infiniteNeg_add_not_infinitePos`：infiniteNeg_add_not_infiniteP
os {x y : Real*} : InfiniteNeg x -> ¬InfinitePos y -> InfiniteNeg (x + y)
· 使用定理 `Hyperreal.InfiniteNeg.not_infinitePos`：∀ {x : ℝ*}, x.InfiniteNeg → ¬x.In
finitePos
-/
theorem infiniteNeg_add_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx hy.not_infinitePos

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_add_not_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_add_not_infinite {x y : Real*} : InfinitePos x -> ¬Infinite y 
-> InfinitePos (x + y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitePos_add_not_infiniteNeg`：infinitePos_add_not_infiniteN
eg {x y : Real*} : InfinitePos x -> ¬InfiniteNeg y -> InfinitePos (x + y)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem infinitePos_add_not_infinite {x y : ℝ*} :
    InfinitePos x → ¬Infinite y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (not_or.mp hy).2

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_add_not_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_add_not_infinite {x y : Real*} : InfiniteNeg x -> ¬Infinite y 
-> InfiniteNeg (x + y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infiniteNeg_add_not_infinitePos`：infiniteNeg_add_not_infiniteP
os {x y : Real*} : InfiniteNeg x -> ¬InfinitePos y -> InfiniteNeg (x + y)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem infiniteNeg_add_not_infinite {x y : ℝ*} :
    InfiniteNeg x → ¬Infinite y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (not_or.mp hy).1

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_of_tendsto_top** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_of_tendsto_top {f : Nat -> Real} (hf : Tendsto f atTop atTop) 
: InfinitePos (ofSeq f)
参数：hf : Tendsto f atTop atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Nat.hyperfilter_le_atTop`：↑(Filter.hyperfilter ℕ) ≤ Filter.atTop
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.infinitePos_iff`：infinitePos_iff {x : Real*} : InfinitePos x ↔
 0 < x ∧ mk x < 0
· 使用定理 `Hyperreal.lt_of_tendsto_atTop`：lt_of_tendsto_atTop {x : Real*} (r : Real
) (hx : x.Tendsto atTop) : r < x
· 使用定理 `Hyperreal.archimedeanClassMk_neg_of_tendsto_atTop`：archimedeanClassMk_ne
g_of_tendsto_atTop {x : Real*} (hx : x.Tendsto atTop) : mk x < 0
-/
theorem infinitePos_of_tendsto_top {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    InfinitePos (ofSeq f) := by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infinitePos_iff]
  exact ⟨lt_of_tendsto_atTop 0 hf, archimedeanClassMk_neg_of_tendsto_atTop hf⟩

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_of_tendsto_bot** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_of_tendsto_bot {f : Nat -> Real} (hf : Tendsto f atTop atBot) 
: InfiniteNeg (ofSeq f)
参数：hf : Tendsto f atTop atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Nat.hyperfilter_le_atTop`：↑(Filter.hyperfilter ℕ) ≤ Filter.atTop
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.infiniteNeg_iff`：infiniteNeg_iff {x : Real*} : InfiniteNeg x ↔
 x < 0 ∧ mk x < 0
· 使用定理 `Hyperreal.lt_of_tendsto_atBot`：lt_of_tendsto_atBot {x : Real*} (r : Real
) (hx : x.Tendsto atBot) : x < r
· 使用定理 `Hyperreal.archimedeanClassMk_neg_of_tendsto_atBot`：archimedeanClassMk_ne
g_of_tendsto_atBot {x : Real*} (hx : x.Tendsto atBot) : mk x < 0
-/
theorem infiniteNeg_of_tendsto_bot {f : ℕ → ℝ} (hf : Tendsto f atTop atBot) :
    InfiniteNeg (ofSeq f) := by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infiniteNeg_iff]
  exact ⟨lt_of_tendsto_atBot 0 hf, archimedeanClassMk_neg_of_tendsto_atBot hf⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.not_infinite_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：not_infinite_neg {x : Real*} : ¬Infinite x -> ¬Infinite (-x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Hyperreal.infinite_neg`：infinite_neg {x : Real*} : Infinite (-x) ↔ Infin
ite x
-/
theorem not_infinite_neg {x : ℝ*} : ¬Infinite x → ¬Infinite (-x) := mt infinite_neg.mp

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.not_infinite_add** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：not_infinite_add {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬In
finite (x + y)
参数：hx : ¬Infinite x；hy : ¬Infinite y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.exists_st_of_not_infinite`：exists_st_of_not_infinite {x : Real
*} (hni : ¬Infinite x) : exists r : Real, IsSt x r
· 使用定理 `Hyperreal.not_infinite_of_exists_st`：not_infinite_of_exists_st {x : Real
*} : (exists r : Real, IsSt x r) -> ¬Infinite x
· 使用定理 `Hyperreal.IsSt.add`：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → (x + y
).IsSt (r + s)
-/
theorem not_infinite_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x + y) :=
  have ⟨r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨s, hs⟩ := exists_st_of_not_infinite hy
  not_infinite_of_exists_st <| ⟨r + s, hr.add hs⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.not_infinite_iff_exist_lt_gt** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：not_infinite_iff_exist_lt_gt {x : Real*} : ¬Infinite x ↔ exists r s : Real
, (r : Real*) < x ∧ x < s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.exists_st_of_not_infinite`：exists_st_of_not_infinite {x : Real
*} (hni : ¬Infinite x) : exists r : Real, IsSt x r
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬Infinite x ↔ ∃ r s : ℝ, (r : ℝ*) < x ∧ x < s :=
  ⟨fun hni ↦ let ⟨r, hr⟩ := exists_st_of_not_infinite hni; ⟨r - 1, r + 1, hr 1 one_pos⟩,
    fun ⟨r, s, hr, hs⟩ hi ↦ hi.elim (fun hp ↦ (hp s).not_gt hs) (fun hn ↦ (hn r).not_gt hr)⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.not_infinite_real** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：not_infinite_real (r : Real) : ¬Infinite r
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.not_infinite_iff_exist_lt_gt`：not_infinite_iff_exist_lt_gt {x 
: Real*} : ¬Infinite x ↔ exists r s : Real, (r : Real*) < x ∧ x < s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.coe_lt_coe`：coe_lt_coe {x y : Real} : (x : Real*) < y ↔ x < y
· 使用引理 `sub_one_lt`：sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStric
tMono R] (a : R) : a - 1 < a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
-/
theorem not_infinite_real (r : ℝ) : ¬Infinite r := by
  rw [not_infinite_iff_exist_lt_gt]
  exact ⟨r - 1, r + 1, coe_lt_coe.2 <| sub_one_lt r, coe_lt_coe.2 <| lt_add_one r⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.Infinite.ne_real** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.Infinite`。
形式化陈述：∀ {x : ℝ*}, x.Infinite → ∀ (r : ℝ), x ≠ ↑r
参数：r : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.not_infinite_real`：not_infinite_real (r : Real) : ¬Infinite r
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
-/
theorem Infinite.ne_real {x : ℝ*} : Infinite x → ∀ r : ℝ, x ≠ r := fun hi r hr =>
  not_infinite_real r <| @Eq.subst _ Infinite _ _ hr hi

/-!
### Facts about `st` that require some infinite machinery
-/

@[deprecated stdPart_mul (since := "2026-01-05")]
/-
**Hyperreal.IsSt.mul** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → (x * y).IsSt (r * s)
参数：x * y；r * s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.map₂`：∀ {x y : ℝ*} {r s : ℝ},   x.IsSt r →     y.IsSt s →
       ∀ {f : ℝ → ℝ → ℝ}, ContinuousAt (Function.uncurry f) (r, s) → Hyperreal.I
sSt (Filt…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ

--- 原说明 ---
### Facts about `st` that require some infinite machinery
-/
theorem IsSt.mul {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x * y) (r * s) :=
  hxr.map₂ hys continuous_mul.continuousAt

@[deprecated mk_mul (since := "2026-01-05")]
/-
**Hyperreal.not_infinite_mul** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：not_infinite_mul {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬In
finite (x * y)
参数：hx : ¬Infinite x；hy : ¬Infinite y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.exists_st_of_not_infinite`：exists_st_of_not_infinite {x : Real
*} (hni : ¬Infinite x) : exists r : Real, IsSt x r
· 使用定理 `Hyperreal.IsSt.not_infinite`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → ¬x.Infinite
· 使用定理 `Hyperreal.IsSt.mul`：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → (x * y
).IsSt (r * s)
-/
theorem not_infinite_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x * y) :=
  have ⟨_r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨_s, hs⟩ := exists_st_of_not_infinite hy
  (hr.mul hs).not_infinite

@[deprecated stdPart_add (since := "2026-01-05")]
/-
**Hyperreal.st_add** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：st_add {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x + y) = 
st x + st y
参数：hx : ¬Infinite x；hy : ¬Infinite y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.unique`：∀ {x : ℝ*} {r s : ℝ}, x.IsSt r → x.IsSt s → r = s
· 使用定理 `Hyperreal.isSt_st'`：isSt_st' {x : Real*} (hx : ¬Infinite x) : IsSt x (st
 x)
· 使用定理 `Hyperreal.not_infinite_add`：not_infinite_add {x y : Real*} (hx : ¬Infini
te x) (hy : ¬Infinite y) : ¬Infinite (x + y)
· 使用定理 `Hyperreal.IsSt.add`：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → (x + y
).IsSt (r + s)
-/
theorem st_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x + y) = st x + st y :=
  (isSt_st' (not_infinite_add hx hy)).unique ((isSt_st' hx).add (isSt_st' hy))

@[deprecated stdPart_neg (since := "2026-01-05")]
/-
**Hyperreal.st_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：st_neg (x : Real*) : st (-x) = -st x
参数：x : Real*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.Infinite.st_eq`：∀ {x : ℝ*}, x.Infinite → x.st = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.infinite_neg`：infinite_neg {x : Real*} : Infinite (-x) ↔ Infin
ite x
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Hyperreal.IsSt.unique`：∀ {x : ℝ*} {r s : ℝ}, x.IsSt r → x.IsSt s → r = s
· 使用定理 `Hyperreal.isSt_st'`：isSt_st' {x : Real*} (hx : ¬Infinite x) : IsSt x (st
 x)
· 使用定理 `Hyperreal.not_infinite_neg`：not_infinite_neg {x : Real*} : ¬Infinite x -
> ¬Infinite (-x)
· 使用定理 `Hyperreal.IsSt.neg`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → (-x).IsSt (-r)
-/
theorem st_neg (x : ℝ*) : st (-x) = -st x := by
  by_cases h : Infinite x
  · rw [h.st_eq, (infinite_neg.2 h).st_eq, neg_zero]
  · exact (isSt_st' (not_infinite_neg h)).unique (isSt_st' h).neg

@[deprecated stdPart_mul (since := "2026-01-05")]
/-
**Hyperreal.st_mul** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：st_mul {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x * y) = 
st x * st y
参数：hx : ¬Infinite x；hy : ¬Infinite y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.isSt_st'`：isSt_st' {x : Real*} (hx : ¬Infinite x) : IsSt x (st
 x)
· 使用定理 `Hyperreal.not_infinite_mul`：not_infinite_mul {x y : Real*} (hx : ¬Infini
te x) (hy : ¬Infinite y) : ¬Infinite (x * y)
· 使用定理 `Hyperreal.IsSt.unique`：∀ {x : ℝ*} {r s : ℝ}, x.IsSt r → x.IsSt s → r = s
· 使用定理 `Hyperreal.IsSt.mul`：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → (x * y
).IsSt (r * s)
-/
theorem st_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x * y) = st x * st y :=
  have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_mul hx hy)
  hxy.unique (hx'.mul hy')

/-!
### Basic lemmas about infinitesimal
-/

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_def** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitesimal_def {x : Real*} : Infinitesimal x ↔ forall r : Real, 0 < r -
> -(r : Real*) < x ∧ x < r
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Basic lemmas about infinitesimal
-/
theorem infinitesimal_def {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, 0 < r → -(r : ℝ*) < x ∧ x < r := by
  simp [Infinitesimal, IsSt]

@[deprecated lt_of_pos_of_archimedean (since := "2026-01-05")]
/-
**Hyperreal.lt_of_pos_of_infinitesimal** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：lt_of_pos_of_infinitesimal {x : Real*} : Infinitesimal x -> forall r : Rea
l, 0 < r -> x < r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Hyperreal.infinitesimal_def`：infinitesimal_def {x : Real*} : Infinitesim
al x ↔ forall r : Real, 0 < r -> -(r : Real*) < x ∧ x < r
-/
theorem lt_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → x < r :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).2

@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]
/-
**Hyperreal.lt_neg_of_pos_of_infinitesimal** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`
。
形式化陈述：lt_neg_of_pos_of_infinitesimal {x : Real*} : Infinitesimal x -> forall r :
 Real, 0 < r -> -↑r < x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Hyperreal.infinitesimal_def`：infinitesimal_def {x : Real*} : Infinitesim
al x ↔ forall r : Real, 0 < r -> -(r : Real*) < x ∧ x < r
-/
theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → -↑r < x :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).1

@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]
/-
**Hyperreal.gt_of_neg_of_infinitesimal** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：gt_of_neg_of_infinitesimal {x : Real*} (hi : Infinitesimal x) (r : Real) (
hr : r < 0) : ↑r < x
参数：hi : Infinitesimal x；r : Real；hr : r < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Hyperreal.infinitesimal_def`：infinitesimal_def {x : Real*} : Infinitesim
al x ↔ forall r : Real, 0 < r -> -(r : Real*) < x ∧ x < r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem gt_of_neg_of_infinitesimal {x : ℝ*} (hi : Infinitesimal x) (r : ℝ) (hr : r < 0) : ↑r < x :=
  neg_neg r ▸ (infinitesimal_def.1 hi (-r) (neg_pos.2 hr)).1

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.abs_lt_real_iff_infinitesimal** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：abs_lt_real_iff_infinitesimal {x : Real*} : Infinitesimal x ↔ forall r : R
eal, r != 0 -> |x| < |↑r|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Hyperreal.infinitesimal_def`：infinitesimal_def {x : Real*} : Infinitesim
al x ↔ forall r : Real, 0 < r -> -(r : Real*) < x ∧ x < r
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `Hyperreal.coe_abs`：coe_abs (x : Real) : ((|x| : Real) : Real*) = |↑x|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `Hyperreal.coe_pos`：coe_pos {x : Real} : 0 < (x : Real*) ↔ 0 < x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → |x| < |↑r| :=
  ⟨fun hi r hr ↦ abs_lt.mpr (coe_abs r ▸ infinitesimal_def.mp hi |r| (abs_pos.2 hr)), fun hR ↦
    infinitesimal_def.mpr fun r hr => abs_lt.mp <| (abs_of_pos <| coe_pos.2 hr) ▸ hR r <| hr.ne'⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitesimal_zero : Infinitesimal 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.isSt_refl_real`：isSt_refl_real (r : Real) : IsSt r r
-/
theorem infinitesimal_zero : Infinitesimal 0 := isSt_refl_real 0

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.Infinitesimal.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.Infinites
imal`。
形式化陈述：∀ {r : ℝ}, (↑r).Infinitesimal → r = 0
参数：↑r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.eq_of_isSt_real`：eq_of_isSt_real {r s : Real} : IsSt r s -> r 
= s
-/
theorem Infinitesimal.eq_zero {r : ℝ} : Infinitesimal r → r = 0 := eq_of_isSt_real

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_real_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitesimal_real_iff {r : Real} : Infinitesimal r ↔ r = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.isSt_real_iff_eq`：isSt_real_iff_eq {r s : Real} : IsSt r s ↔ r
 = s
-/
theorem infinitesimal_real_iff {r : ℝ} : Infinitesimal r ↔ r = 0 :=
  isSt_real_iff_eq

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.add {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by simpa only [add_zero] using! hx.add hy

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.neg {x : ℝ*} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  simpa only [neg_zero] using! hx.neg

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitesimal_neg {x : Real*} : Infinitesimal (-x) ↔ Infinitesimal x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.Infinitesimal.neg`：∀ {x : ℝ*}, x.Infinitesimal → (-x).Infinite
simal
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem infinitesimal_neg {x : ℝ*} : Infinitesimal (-x) ↔ Infinitesimal x :=
  ⟨fun h => neg_neg x ▸ h.neg, Infinitesimal.neg⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.mul {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by simpa only [mul_zero] using! hx.mul hy

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_of_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitesimal_of_tendsto_zero {f : Nat -> Real} (h : Tendsto f atTop (𝓝 0)
) : Infinitesimal (ofSeq f)
参数：h : Tendsto f atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.isSt_of_tendsto`：isSt_of_tendsto {f : Nat -> Real} {r : Real} 
(hf : Tendsto f atTop (𝓝 r)) : IsSt (ofSeq f) r
-/
theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) :
    Infinitesimal (ofSeq f) :=
  isSt_of_tendsto h

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_epsilon** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitesimal_epsilon : Infinitesimal ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitesimal_of_tendsto_zero`：infinitesimal_of_tendsto_zero {
f : Nat -> Real} (h : Tendsto f atTop (𝓝 0)) : Infinitesimal (ofSeq f)
· 使用定理 `tendsto_inv_atTop_nhds_zero_nat`：tendsto_inv_atTop_nhds_zero_nat {𝕜 : Ty
pe*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>
=0 𝕜] : Tendsto (fun …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNRat.instContinuousSMulOfIsScalarTowerOfRat`：∀ {R : Type u_1} [inst : T
opologicalSpace R] [inst_1 : MulAction ℚ R] [inst_2 : MulAction ℚ≥0 R] [IsScalar
Tower ℚ≥0 ℚ R]   [ContinuousSMul ℚ…
· 使用定理 `NNRat.instContinuousSMulRatReal`：ContinuousSMul ℚ ℝ
-/
theorem infinitesimal_epsilon : Infinitesimal ε :=
  infinitesimal_of_tendsto_zero tendsto_inv_atTop_nhds_zero_nat

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.not_real_of_infinitesimal_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hyperre
al`。
形式化陈述：not_real_of_infinitesimal_ne_zero (x : Real*) : Infinitesimal x -> x != 0 
-> forall r : Real, x != r
参数：x : Real*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.coe_eq_zero`：coe_eq_zero {x : Real} : (x : Real*) = 0 ↔ x = 0
· 使用定理 `Hyperreal.IsSt.unique`：∀ {x : ℝ*} {r s : ℝ}, x.IsSt r → x.IsSt s → r = s
· 使用定理 `Hyperreal.isSt_refl_real`：isSt_refl_real (r : Real) : IsSt r r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem not_real_of_infinitesimal_ne_zero (x : ℝ*) : Infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ r :=
  fun hi hx r hr =>
  hx <| hr.trans <| coe_eq_zero.2 <| IsSt.unique (hr.symm ▸ isSt_refl_real r : IsSt x r) hi

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.IsSt.infinitesimal_sub** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → (x - ↑r).Infinitesimal
参数：x - ↑r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Hyperreal.IsSt.sub`：∀ {x y : ℝ*} {r s : ℝ}, x.IsSt r → y.IsSt s → (x - y
).IsSt (r - s)
· 使用定理 `Hyperreal.isSt_refl_real`：isSt_refl_real (r : Real) : IsSt r r
-/
theorem IsSt.infinitesimal_sub {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : Infinitesimal (x - ↑r) := by
  simpa only [sub_self] using! hxr.sub (isSt_refl_real r)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_sub_st** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitesimal_sub_st {x : Real*} (hx : ¬Infinite x) : Infinitesimal (x - ↑
(st x))
参数：hx : ¬Infinite x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.infinitesimal_sub`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → (x - ↑r
).Infinitesimal
· 使用定理 `Hyperreal.isSt_st'`：isSt_st' {x : Real*} (hx : ¬Infinite x) : IsSt x (st
 x)
-/
theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬Infinite x) : Infinitesimal (x - ↑(st x)) :=
  (isSt_st' hx).infinitesimal_sub

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_iff_infinitesimal_inv_pos** 是 Mathlib 中的一个定理，位于命名空间 `Hyp
erreal`。
形式化陈述：infinitePos_iff_infinitesimal_inv_pos {x : Real*} : InfinitePos x ↔ Infini
tesimal x⁻¹ ∧ 0 < x⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.infinitePos_iff`：infinitePos_iff {x : Real*} : InfinitePos x ↔
 0 < x ∧ mk x < 0
· 使用定理 `Hyperreal.infinitesimal_iff`：infinitesimal_iff {x : Real*} : Infinitesim
al x ↔ 0 < mk x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem infinitePos_iff_infinitesimal_inv_pos {x : ℝ*} :
    InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹ := by
  rw [infinitePos_iff, infinitesimal_iff]
  aesop

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_iff_infinitesimal_inv_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hyp
erreal`。
形式化陈述：infiniteNeg_iff_infinitesimal_inv_neg {x : Real*} : InfiniteNeg x ↔ Infini
tesimal x⁻¹ ∧ x⁻¹ < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Hyperreal.infinitePos_neg`：infinitePos_neg {x : Real*} : InfinitePos (-x
) ↔ InfiniteNeg x
· 使用定理 `Hyperreal.infinitePos_iff_infinitesimal_inv_pos`：infinitePos_iff_infinit
esimal_inv_pos {x : Real*} : InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Hyperreal.infinitesimal_neg`：infinitesimal_neg {x : Real*} : Infinitesim
al (-x) ↔ Infinitesimal x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infiniteNeg_iff_infinitesimal_inv_neg {x : ℝ*} :
    InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0 := by
  rw [← infinitePos_neg, infinitePos_iff_infinitesimal_inv_pos, inv_neg, neg_pos, infinitesimal_neg]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_inv_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitesimal_inv_of_infinite {x : Real*} : Infinite x -> Infinitesimal x⁻
¹
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Hyperreal.infinitePos_iff_infinitesimal_inv_pos`：infinitePos_iff_infinit
esimal_inv_pos {x : Real*} : InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹
· 使用定理 `Hyperreal.infiniteNeg_iff_infinitesimal_inv_neg`：infiniteNeg_iff_infinit
esimal_inv_neg {x : Real*} : InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0
-/
theorem infinitesimal_inv_of_infinite {x : ℝ*} : Infinite x → Infinitesimal x⁻¹ := fun hi =>
  Or.casesOn hi (fun hip => (infinitePos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infiniteNeg_iff_infinitesimal_inv_neg.mp hin).1

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinite_of_infinitesimal_inv** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinite_of_infinitesimal_inv {x : Real*} (h0 : x != 0) (hi : Infinitesima
l x⁻¹) : Infinite x
参数：h0 : x != 0；hi : Infinitesimal x⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.infiniteNeg_iff_infinitesimal_inv_neg`：infiniteNeg_iff_infinit
esimal_inv_neg {x : Real*} : InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0
· 使用定理 `inv_lt_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linea
rOrder G₀] {a : G₀} [PosMulMono G₀], a⁻¹ < 0 ↔ a < 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `Hyperreal.infinitePos_iff_infinitesimal_inv_pos`：infinitePos_iff_infinit
esimal_inv_pos {x : Real*} : InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : Infinitesimal x⁻¹) :
    Infinite x := by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · exact Or.inr (infiniteNeg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
  · exact Or.inl (infinitePos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinite_iff_infinitesimal_inv** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`
。
形式化陈述：infinite_iff_infinitesimal_inv {x : Real*} (h0 : x != 0) : Infinite x ↔ In
finitesimal x⁻¹
参数：h0 : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitesimal_inv_of_infinite`：infinitesimal_inv_of_infinite {
x : Real*} : Infinite x -> Infinitesimal x⁻¹
· 使用定理 `Hyperreal.infinite_of_infinitesimal_inv`：infinite_of_infinitesimal_inv {
x : Real*} (h0 : x != 0) (hi : Infinitesimal x⁻¹) : Infinite x
-/
theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : Infinite x ↔ Infinitesimal x⁻¹ :=
  ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_pos_iff_infinitePos_inv** 是 Mathlib 中的一个定理，位于命名空间 `Hyp
erreal`。
形式化陈述：infinitesimal_pos_iff_infinitePos_inv {x : Real*} : InfinitePos x⁻¹ ↔ Infi
nitesimal x ∧ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Hyperreal.infinitePos_iff_infinitesimal_inv_pos`：infinitePos_iff_infinit
esimal_inv_pos {x : Real*} : InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infinitesimal_pos_iff_infinitePos_inv {x : ℝ*} :
    InfinitePos x⁻¹ ↔ Infinitesimal x ∧ 0 < x :=
  infinitePos_iff_infinitesimal_inv_pos.trans <| by rw [inv_inv]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_neg_iff_infiniteNeg_inv** 是 Mathlib 中的一个定理，位于命名空间 `Hyp
erreal`。
形式化陈述：infinitesimal_neg_iff_infiniteNeg_inv {x : Real*} : InfiniteNeg x⁻¹ ↔ Infi
nitesimal x ∧ x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Hyperreal.infiniteNeg_iff_infinitesimal_inv_neg`：infiniteNeg_iff_infinit
esimal_inv_neg {x : Real*} : InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infinitesimal_neg_iff_infiniteNeg_inv {x : ℝ*} :
    InfiniteNeg x⁻¹ ↔ Infinitesimal x ∧ x < 0 :=
  infiniteNeg_iff_infinitesimal_inv_neg.trans <| by rw [inv_inv]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitesimal_iff_infinite_inv** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`
。
形式化陈述：infinitesimal_iff_infinite_inv {x : Real*} (h : x != 0) : Infinitesimal x 
↔ Infinite x⁻¹
参数：h : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Hyperreal.infinite_iff_infinitesimal_inv`：infinite_iff_infinitesimal_inv
 {x : Real*} (h0 : x != 0) : Infinite x ↔ Infinitesimal x⁻¹
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : Infinitesimal x ↔ Infinite x⁻¹ :=
  Iff.trans (by rw [inv_inv]) (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm

@[deprecated stdPart_inv (since := "2026-01-05")]
/-
**Hyperreal.IsSt.inv** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.IsSt`。
形式化陈述：∀ {x : ℝ*} {r : ℝ}, ¬x.Infinitesimal → x.IsSt r → x⁻¹.IsSt r⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.IsSt.map`：∀ {x : ℝ*} {r : ℝ}, x.IsSt r → ∀ {f : ℝ → ℝ}, Contin
uousAt f r → Hyperreal.IsSt (Filter.Germ.map f x) (f r)
· 使用定理 `ContinuousInv₀.continuousAt_inv₀`：∀ {G₀ : Type u_4} {inst : Zero G₀} {in
st_1 : Inv G₀} {inst_2 : TopologicalSpace G₀} [self : ContinuousInv₀ G₀] ⦃x : G₀
⦄,   x ≠ 0 → Continuou…
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsSt.inv {x : ℝ*} {r : ℝ} (hi : ¬Infinitesimal x) (hr : IsSt x r) : IsSt x⁻¹ r⁻¹ :=
  hr.map <| continuousAt_inv₀ <| by rintro rfl; exact hi hr

@[deprecated stdPart_inv (since := "2026-01-05")]
/-
**Hyperreal.st_inv** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：st_inv (x : Real*) : st x⁻¹ = (st x)⁻¹
参数：x : Real*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hyperreal.st_eq`：st_eq (x : Real*) : st x = stdPart x
· 使用定理 `ArchimedeanClass.stdPart_inv`：stdPart_inv (x : K) : stdPart x⁻¹ = (stdPa
rt x)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ := by
  simp [st_eq]

@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_omega** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_omega : InfinitePos ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.infinitePos_iff_infinitesimal_inv_pos`：infinitePos_iff_infinit
esimal_inv_pos {x : Real*} : InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹
· 使用定理 `Hyperreal.infinitesimal_epsilon`：infinitesimal_epsilon : Infinitesimal ε
· 使用定理 `Hyperreal.epsilon_pos`：epsilon_pos : 0 < ε
-/
theorem infinitePos_omega : InfinitePos ω :=
  infinitePos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]
/-
**Hyperreal.infinite_omega** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinite_omega : Infinite ω
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.infinite_iff_infinitesimal_inv`：infinite_iff_infinitesimal_inv
 {x : Real*} (h0 : x != 0) : Infinite x ↔ Infinitesimal x⁻¹
· 使用定理 `Hyperreal.omega_ne_zero`：omega_ne_zero : ω != 0
· 使用定理 `Hyperreal.infinitesimal_epsilon`：infinitesimal_epsilon : Infinitesimal ε
-/
theorem infinite_omega : Infinite ω :=
  (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos** 是 Mathlib 中的一
个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_mul_of_infinitePos_not_infinitesimal_pos {x y : Real*} : Infin
itePos x -> ¬Infinitesimal y -> 0 < y -> InfinitePos (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Hyperreal.infinitesimal_def`：infinitesimal_def {x : Real*} : Infinitesim
al x ↔ forall r : Real, 0 < r -> -(r : Real*) < x ∧ x < r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Classical.not_imp`：∀ {a b : Prop}, ¬(a → b) ↔ a ∧ ¬b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Hyperreal.coe_mul`：coe_mul (x y : Real) : ↑(x * y) = (x * y : Real*)
· 使用定理 `mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α]   [MulPosStrictMono α], a < b → c ≤ d →
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Hyperreal.coe_lt_coe`：coe_lt_coe {x y : Real} : (x : Real*) < y ↔ x < y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem infinitePos_mul_of_infinitePos_not_infinitesimal_pos {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → 0 < y → InfinitePos (x * y) := fun hx hy₁ hy₂ r => by
  have hy₁' := not_forall.mp (mt infinitesimal_def.2 hy₁)
  let ⟨r₁, hy₁''⟩ := hy₁'
  have hyr : 0 < r₁ ∧ ↑r₁ ≤ y := by
    rwa [Classical.not_imp, ← abs_lt, not_lt, abs_of_pos hy₂] at hy₁''
  rw [← div_mul_cancel₀ r (ne_of_gt hyr.1), coe_mul]
  exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_lt (hx 0))

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_mul_of_not_infinitesimal_pos_infinitePos** 是 Mathlib 中的一
个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_mul_of_not_infinitesimal_pos_infinitePos {x y : Real*} : ¬Infi
nitesimal x -> 0 < x -> InfinitePos y -> InfinitePos (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos`：infinite
Pos_mul_of_infinitePos_not_infinitesimal_pos {x y : Real*} : InfinitePos x -> ¬I
nfinitesimal y -> 0 < y -> InfinitePos (x * y)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem infinitePos_mul_of_not_infinitesimal_pos_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfinitePos y → InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infinitePos_not_infinitesimal_pos hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg** 是 Mathlib 中的一
个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : Real*} : Infin
iteNeg x -> ¬Infinitesimal y -> y < 0 -> InfinitePos (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Hyperreal.infinitePos_neg`：infinitePos_neg {x : Real*} : InfinitePos (-x
) ↔ InfiniteNeg x
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `Hyperreal.infinitesimal_neg`：infinitesimal_neg {x : Real*} : Infinitesim
al (-x) ↔ Infinitesimal x
· 使用定理 `Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos`：infinite
Pos_mul_of_infinitePos_not_infinitesimal_pos {x y : Real*} : InfinitePos x -> ¬I
nfinitesimal y -> 0 < y -> InfinitePos (x * y)
-/
theorem infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → y < 0 → InfinitePos (x * y) := by
  rw [← infinitePos_neg, ← neg_pos, ← neg_mul_neg, ← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg** 是 Mathlib 中的一
个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg {x y : Real*} : ¬Infi
nitesimal x -> x < 0 -> InfiniteNeg y -> InfinitePos (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg`：infinite
Pos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : Real*} : InfiniteNeg x -> ¬I
nfinitesimal y -> y < 0 -> InfinitePos (x * y)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfiniteNeg y → InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg** 是 Mathlib 中的一
个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg {x y : Real*} : Infin
itePos x -> ¬Infinitesimal y -> y < 0 -> InfiniteNeg (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Hyperreal.infinitePos_neg`：infinitePos_neg {x : Real*} : InfinitePos (-x
) ↔ InfiniteNeg x
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Hyperreal.instIsStrictOrderedRing`：IsStrictOrderedRing ℝ*
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `Hyperreal.infinitesimal_neg`：infinitesimal_neg {x : Real*} : Infinitesim
al (-x) ↔ Infinitesimal x
· 使用定理 `Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos`：infinite
Pos_mul_of_infinitePos_not_infinitesimal_pos {x y : Real*} : InfinitePos x -> ¬I
nfinitesimal y -> 0 < y -> InfinitePos (x * y)
-/
theorem infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → y < 0 → InfiniteNeg (x * y) := by
  rw [← infinitePos_neg, ← neg_pos, neg_mul_eq_mul_neg, ← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos** 是 Mathlib 中的一
个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos {x y : Real*} : ¬Infi
nitesimal x -> x < 0 -> InfinitePos y -> InfiniteNeg (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg`：infinite
Neg_mul_of_infinitePos_not_infinitesimal_neg {x y : Real*} : InfinitePos x -> ¬I
nfinitesimal y -> y < 0 -> InfiniteNeg (x * y)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfinitePos y → InfiniteNeg (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos** 是 Mathlib 中的一
个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : Real*} : Infin
iteNeg x -> ¬Infinitesimal y -> 0 < y -> InfiniteNeg (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Hyperreal.infinitePos_neg`：infinitePos_neg {x : Real*} : InfinitePos (-x
) ↔ InfiniteNeg x
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用定理 `Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos`：infinite
Pos_mul_of_infinitePos_not_infinitesimal_pos {x y : Real*} : InfinitePos x -> ¬I
nfinitesimal y -> 0 < y -> InfinitePos (x * y)
-/
theorem infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → 0 < y → InfiniteNeg (x * y) := by
  rw [← infinitePos_neg, ← infinitePos_neg, neg_mul_eq_neg_mul]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg** 是 Mathlib 中的一
个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg {x y : Real*} : ¬Infi
nitesimal x -> 0 < x -> InfiniteNeg y -> InfiniteNeg (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Hyperreal.infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos`：infinite
Neg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : Real*} : InfiniteNeg x -> ¬I
nfinitesimal y -> 0 < y -> InfiniteNeg (x * y)
-/
theorem infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm]; exact infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_mul_infinitePos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_mul_infinitePos {x y : Real*} : InfinitePos x -> InfinitePos y
 -> InfinitePos (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos`：infinite
Pos_mul_of_infinitePos_not_infinitesimal_pos {x y : Real*} : InfinitePos x -> ¬I
nfinitesimal y -> 0 < y -> InfinitePos (x * y)
· 使用定理 `Hyperreal.InfinitePos.not_infinitesimal`：∀ {x : ℝ*}, x.InfinitePos → ¬x.
Infinitesimal
-/
theorem infinitePos_mul_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infinitePos_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_mul_infiniteNeg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_mul_infiniteNeg {x y : Real*} : InfiniteNeg x -> InfiniteNeg y
 -> InfinitePos (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg`：infinite
Pos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : Real*} : InfiniteNeg x -> ¬I
nfinitesimal y -> y < 0 -> InfinitePos (x * y)
· 使用定理 `Hyperreal.InfiniteNeg.not_infinitesimal`：∀ {x : ℝ*}, x.InfiniteNeg → ¬x.
Infinitesimal
-/
theorem infiniteNeg_mul_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinitePos_mul_infiniteNeg** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infinitePos_mul_infiniteNeg {x y : Real*} : InfinitePos x -> InfiniteNeg y
 -> InfiniteNeg (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg`：infinite
Neg_mul_of_infinitePos_not_infinitesimal_neg {x y : Real*} : InfinitePos x -> ¬I
nfinitesimal y -> y < 0 -> InfiniteNeg (x * y)
· 使用定理 `Hyperreal.InfiniteNeg.not_infinitesimal`：∀ {x : ℝ*}, x.InfiniteNeg → ¬x.
Infinitesimal
-/
theorem infinitePos_mul_infiniteNeg {x y : ℝ*} :
    InfinitePos x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infiniteNeg_mul_infinitePos** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal`。
形式化陈述：infiniteNeg_mul_infinitePos {x y : Real*} : InfiniteNeg x -> InfinitePos y
 -> InfiniteNeg (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos`：infinite
Neg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : Real*} : InfiniteNeg x -> ¬I
nfinitesimal y -> 0 < y -> InfiniteNeg (x * y)
· 使用定理 `Hyperreal.InfinitePos.not_infinitesimal`：∀ {x : ℝ*}, x.InfinitePos → ¬x.
Infinitesimal
-/
theorem infiniteNeg_mul_infinitePos {x y : ℝ*} :
    InfiniteNeg x → InfinitePos y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinite_mul_of_infinite_not_infinitesimal** 是 Mathlib 中的一个定理，位于命名空间
 `Hyperreal`。
形式化陈述：infinite_mul_of_infinite_not_infinitesimal {x y : Real*} : Infinite x -> ¬
Infinitesimal y -> Infinite (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Hyperreal.isSt_refl_real`：isSt_refl_real (r : Real) : IsSt r r
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Hyperreal.infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg`：infinite
Neg_mul_of_infinitePos_not_infinitesimal_neg {x y : Real*} : InfinitePos x -> ¬I
nfinitesimal y -> y < 0 -> InfiniteNeg (x * y)
· 使用定理 `Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos`：infinite
Pos_mul_of_infinitePos_not_infinitesimal_pos {x y : Real*} : InfinitePos x -> ¬I
nfinitesimal y -> 0 < y -> InfinitePos (x * y)
· 使用定理 `Hyperreal.infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg`：infinite
Pos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : Real*} : InfiniteNeg x -> ¬I
nfinitesimal y -> y < 0 -> InfinitePos (x * y)
· 使用定理 `Hyperreal.infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos`：infinite
Neg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : Real*} : InfiniteNeg x -> ¬I
nfinitesimal y -> 0 < y -> InfiniteNeg (x * y)
-/
theorem infinite_mul_of_infinite_not_infinitesimal {x y : ℝ*} :
    Infinite x → ¬Infinitesimal y → Infinite (x * y) := fun hx hy =>
  have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_ne fun H0 => hy (Eq.substr H0 (isSt_refl_real 0))
  hx.elim
    (h0.elim
      (fun H0 Hx => Or.inr (infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inl (infinitePos_mul_of_infinitePos_not_infinitesimal_pos Hx hy H0))
    (h0.elim
      (fun H0 Hx => Or.inl (infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inr (infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos Hx hy H0))

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.infinite_mul_of_not_infinitesimal_infinite** 是 Mathlib 中的一个定理，位于命名空间
 `Hyperreal`。
形式化陈述：infinite_mul_of_not_infinitesimal_infinite {x y : Real*} : ¬Infinitesimal 
x -> Infinite y -> Infinite (x * y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Hyperreal.infinite_mul_of_infinite_not_infinitesimal`：infinite_mul_of_in
finite_not_infinitesimal {x y : Real*} : Infinite x -> ¬Infinitesimal y -> Infin
ite (x * y)
-/
theorem infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} :
    ¬Infinitesimal x → Infinite y → Infinite (x * y) := fun hx hy => by
  rw [mul_comm]; exact infinite_mul_of_infinite_not_infinitesimal hy hx

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/-
**Hyperreal.Infinite.mul** 是 Mathlib 中的一个定理，位于命名空间 `Hyperreal.Infinite`。
形式化陈述：∀ {x y : ℝ*}, x.Infinite → y.Infinite → (x * y).Infinite
参数：x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hyperreal.infinite_mul_of_infinite_not_infinitesimal`：infinite_mul_of_in
finite_not_infinitesimal {x y : Real*} : Infinite x -> ¬Infinitesimal y -> Infin
ite (x * y)
· 使用定理 `Hyperreal.Infinite.not_infinitesimal`：∀ {x : ℝ*}, x.Infinite → ¬x.Infini
tesimal
-/
theorem Infinite.mul {x y : ℝ*} : Infinite x → Infinite y → Infinite (x * y) := fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx hy.not_infinitesimal

end Hyperreal
end

/-
Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore `positivity` plugin

namespace Tactic

open Positivity

private theorem hyperreal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : ℝ*) ≠ 0 :=
  Hyperreal.coe_ne_zero.2

private theorem hyperreal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : ℝ*) :=
  Hyperreal.coe_nonneg.2

private theorem hyperreal_coe_pos {r : ℝ} : 0 < r → 0 < (r : ℝ*) :=
  Hyperreal.coe_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ℝ*`. -/
@[positivity]
unsafe def positivity_coe_real_hyperreal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ Hyperreal.hasCoeT)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` hyperreal_coe_pos [p]
      | nonnegative p => nonnegative <$> mk_app `` hyperreal_coe_nonneg [p]
      | nonzero p => nonzero <$> mk_app `` hyperreal_coe_ne_zero [p]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ℝ*)` for `r : ℝ`"

end Tactic
-/

