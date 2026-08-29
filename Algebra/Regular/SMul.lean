/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Push

/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`. The corresponding
predicate is called `IsSMulRegular`.

There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting on a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
Scalar multiplications involving `0` are, of course, all trivial.

The defining property is that an element `a ∈ R` is `M`-regular if the scalar multiplication map
`M → M`, defined by `m ↦ a • m`, is injective.

This property is the direct generalization to modules of the property `IsLeftRegular` defined in
`Algebra/Regular`. Lemma `isLeftRegular_iff` shows that indeed the two notions
coincide.
-/

@[expose] public section


variable {R S : Type*} (M : Type*) {a b : R} {s : S}

/--
Definition of `IsSMulRegular` / `IsSMulRegular` 的定义

English:
definition IsSMulRegular
  signature: [SMul R M] (c : R)
  body: Function.Injective ((c • ·) : M -> M)

中文:
定义 IsSMulRegular
  签名: [标量乘法 R M] (c : R)
  定义体: Function.Injective ((c • ·) : M -> M)

Depends on / 依赖: Function, Function.Injective, Injective
-/
def IsSMulRegular [SMul R M] (c : R) :=
  Function.Injective ((c • ·) : M -> M)

/--
theorem `IsLeftRegular.isSMulRegular` / 定理 `IsLeftRegular.isSMulRegular`

English:
theorem IsLeftRegular.isSMulRegular
  given: [Mul R] {c : R} (h : IsLeftRegular c)
  statement: IsSMulRegular R c
  proof: h

中文:
定理 IsLeftRegular.isSMulRegular
  条件: [乘法 R] {c : R} (h : IsLeftRegular c)
  结论: IsSMulRegular R c
  证明: h
-/
theorem IsLeftRegular.isSMulRegular [Mul R] {c : R} (h : IsLeftRegular c) : IsSMulRegular R c :=
  h

/--
theorem `isLeftRegular_iff` / 定理 `isLeftRegular_iff`

English:
theorem isLeftRegular_iff
  given: [Mul R] {a : R}
  statement: IsLeftRegular a ↔ IsSMulRegular R a
  proof: Iff.rfl

中文:
定理 isLeftRegular_iff
  条件: [乘法 R] {a : R}
  结论: IsLeftRegular a ↔ IsSMulRegular R a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isLeftRegular_iff [Mul R] {a : R} : IsLeftRegular a ↔ IsSMulRegular R a :=
  Iff.rfl

/--
theorem `IsRightRegular.isSMulRegular` / 定理 `IsRightRegular.isSMulRegular`

English:
theorem IsRightRegular.isSMulRegular
  given: [Mul R] {c : R} (h : IsRightRegular c)
  proof: h

中文:
定理 IsRightRegular.isSMulRegular
  条件: [乘法 R] {c : R} (h : IsRightRegular c)
  证明: h
-/
theorem IsRightRegular.isSMulRegular [Mul R] {c : R} (h : IsRightRegular c) :
    IsSMulRegular R (MulOpposite.op c) :=
  h

/--
theorem `isRightRegular_iff` / 定理 `isRightRegular_iff`

English:
theorem isRightRegular_iff
  given: [Mul R] {a : R}
  proof: Iff.rfl

中文:
定理 isRightRegular_iff
  条件: [乘法 R] {a : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isRightRegular_iff [Mul R] {a : R} :
    IsRightRegular a ↔ IsSMulRegular R (MulOpposite.op a) :=
  Iff.rfl

variable {M}

/--
lemma `isSMulRegular_map` / 引理 `isSMulRegular_map`

English:
lemma isSMulRegular_map
  given: [SMul R M] [SMul S M] (f : R -> S) (smul : forall m : M, f a • m = a • m)
  proof: by simp [IsSMulRegular, smul]

protected alias ⟨IsSMulRegular.of_map, IsSMulRegular.map⟩ := isSMulRegular_map

中文:
引理 isSMulRegular_map
  条件: [标量乘法 R M] [标量乘法 S M] (f : R -> S) (smul : 对任意 m : M, f a • m = a • m)
  证明: by simp [IsSMulRegular, smul]

protected alias ⟨IsSMulRegular.of_map, IsSMulRegular.map⟩ := isSMulRegular_map

Depends on / 依赖: IsSMulRegular
-/
lemma isSMulRegular_map [SMul R M] [SMul S M] (f : R -> S) (smul : forall m : M, f a • m = a • m) :
    IsSMulRegular M (f a) ↔ IsSMulRegular M a := by simp [IsSMulRegular, smul]

protected alias ⟨IsSMulRegular.of_map, IsSMulRegular.map⟩ := isSMulRegular_map

namespace IsSMulRegular

/--
theorem `natAbs_iff` / 定理 `natAbs_iff`

English:
theorem natAbs_iff
  given: [SubtractionMonoid M] {n : Int}
  proof: by
  simp_rw [IsSMulRegular, Function.Injective]
  conv_rhs => rw [← n.sign_mul_natAbs]
  obtain h | h | h := n.sign_trichotomy
  · simp [h]
  · simp [Int.sign_eq_zero_iff_zero.mp h]
  · simp [h, neg_zsmul]

中文:
定理 natAbs_iff
  条件: [Subtraction幺半群 M] {n : 整数}
  证明: by
  simp_rw [IsSMulRegular, Function.Injective]
  conv_rhs => rw [← n.sign_mul_natAbs]
  obtain h | h | h := n.sign_trichotomy
  · simp [h]
  · simp [Int.sign_eq_zero_iff_zero.mp h]
  · simp [h, neg_zsmul]
-/
@[simp] theorem natAbs_iff [SubtractionMonoid M] {n : Int} :
    IsSMulRegular M n.natAbs ↔ IsSMulRegular M n := by
  simp_rw [IsSMulRegular, Function.Injective]
  conv_rhs => rw [← n.sign_mul_natAbs]
  obtain h | h | h := n.sign_trichotomy
  · simp [h]
  · simp [Int.sign_eq_zero_iff_zero.mp h]
  · simp [h, neg_zsmul]

section SMul

variable [SMul R M] [SMul R S] [SMul S M] [IsScalarTower R S M]

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (ra : IsSMulRegular M a) (rs : IsSMulRegular M s)
  statement: IsSMulRegular M (a • s)
  proof: fun _ _ ab => rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))

中文:
定理 smul
  条件: (ra : IsSMulRegular M a) (rs : IsSMulRegular M s)
  结论: IsSMulRegular M (a • s)
  证明: fun _ _ ab => rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))

Depends on / 依赖: ab.trans, smul_assoc, symm.trans
-/
theorem smul (ra : IsSMulRegular M a) (rs : IsSMulRegular M s) : IsSMulRegular M (a • s) :=
  fun _ _ ab => rs (ra ((smul_assoc _ _ _).symm.trans (ab.trans (smul_assoc _ _ _))))

/--
theorem `of_smul` / 定理 `of_smul`

English:
theorem of_smul
  given: (a : R) (ab : IsSMulRegular M (a • s))
  statement: IsSMulRegular M s
  proof: @Function.Injective.of_comp _ _ _ (fun m : M => a • m) _ fun c d cd => by
  dsimp only [Function.comp_def] at cd
  rw [← smul_assoc]; rw [← smul_assoc] at cd
  exact ab cd

中文:
定理 of_smul
  条件: (a : R) (ab : IsSMulRegular M (a • s))
  结论: IsSMulRegular M s
  证明: @Function.Injective.of_comp _ _ _ (fun m : M => a • m) _ fun c d cd => by
  dsimp only [Function.comp_def] at cd
  rw [← smul_assoc]; rw [← smul_assoc] at cd
  exact ab cd

Depends on / 依赖: Function, Function.Injective.of_comp, Function.comp_def, Injective, comp_def, of_comp, smul_assoc
-/
theorem of_smul (a : R) (ab : IsSMulRegular M (a • s)) : IsSMulRegular M s :=
  @Function.Injective.of_comp _ _ _ (fun m : M => a • m) _ fun c d cd => by
  dsimp only [Function.comp_def] at cd
  rw [← smul_assoc]; rw [← smul_assoc] at cd
  exact ab cd

/-- An element is `M`-regular if and only if multiplying it on the left by an `M`-regular element
is `M`-regular. -/
@[simp]
/--
theorem `smul_iff` / 定理 `smul_iff`

English:
theorem smul_iff
  given: (b : S) (ha : IsSMulRegular M a)
  statement: IsSMulRegular M (a • b) ↔ IsSMulRegular M b
  proof: ⟨of_smul _, ha.smul⟩

中文:
定理 smul_iff
  条件: (b : S) (ha : IsSMulRegular M a)
  结论: IsSMulRegular M (a • b) ↔ IsSMulRegular M b
  证明: ⟨of_smul _, ha.smul⟩

Depends on / 依赖: ha.smul, of_smul
-/
theorem smul_iff (b : S) (ha : IsSMulRegular M a) : IsSMulRegular M (a • b) ↔ IsSMulRegular M b :=
  ⟨of_smul _, ha.smul⟩

/--
theorem `isLeftRegular` / 定理 `isLeftRegular`

English:
theorem isLeftRegular
  given: [Mul R] {a : R} (h : IsSMulRegular R a)
  statement: IsLeftRegular a
  proof: h

中文:
定理 isLeftRegular
  条件: [乘法 R] {a : R} (h : IsSMulRegular R a)
  结论: IsLeftRegular a
  证明: h
-/
theorem isLeftRegular [Mul R] {a : R} (h : IsSMulRegular R a) : IsLeftRegular a :=
  h

/--
theorem `isRightRegular` / 定理 `isRightRegular`

English:
theorem isRightRegular
  given: [Mul R] {a : R} (h : IsSMulRegular R (MulOpposite.op a))
  proof: h

中文:
定理 isRightRegular
  条件: [乘法 R] {a : R} (h : IsSMulRegular R (MulOpposite.op a))
  证明: h
-/
theorem isRightRegular [Mul R] {a : R} (h : IsSMulRegular R (MulOpposite.op a)) :
    IsRightRegular a :=
  h

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular M a) (rb : IsSMulRegular M b)
  proof: ra.smul rb

中文:
定理 mul
  条件: [乘法 R] [标量塔 R R M] (ra : IsSMulRegular M a) (rb : IsSMulRegular M b)
  证明: ra.smul rb

Depends on / 依赖: ra.smul
-/
theorem mul [Mul R] [IsScalarTower R R M] (ra : IsSMulRegular M a) (rb : IsSMulRegular M b) :
    IsSMulRegular M (a * b) :=
  ra.smul rb

/--
theorem `of_mul` / 定理 `of_mul`

English:
theorem of_mul
  given: [Mul R] [IsScalarTower R R M] (ab : IsSMulRegular M (a * b))
  proof: by
  rw [← smul_eq_mul] at ab
  exact ab.of_smul _

@[simp]

中文:
定理 of_mul
  条件: [乘法 R] [标量塔 R R M] (ab : IsSMulRegular M (a * b))
  证明: by
  rw [← smul_eq_mul] at ab
  exact ab.of_smul _

@[simp]

Depends on / 依赖: ab.of_smul, of_smul, smul_eq_mul
-/
theorem of_mul [Mul R] [IsScalarTower R R M] (ab : IsSMulRegular M (a * b)) :
    IsSMulRegular M b := by
  rw [← smul_eq_mul] at ab
  exact ab.of_smul _

@[simp]
/--
theorem `mul_iff_right` / 定理 `mul_iff_right`

English:
theorem mul_iff_right
  given: [Mul R] [IsScalarTower R R M] (ha : IsSMulRegular M a)
  proof: ⟨of_mul, ha.mul⟩

中文:
定理 mul_iff_right
  条件: [乘法 R] [标量塔 R R M] (ha : IsSMulRegular M a)
  证明: ⟨of_mul, ha.mul⟩

Depends on / 依赖: ha.mul, of_mul
-/
theorem mul_iff_right [Mul R] [IsScalarTower R R M] (ha : IsSMulRegular M a) :
    IsSMulRegular M (a * b) ↔ IsSMulRegular M b :=
  ⟨of_mul, ha.mul⟩

/--
theorem `mul_and_mul_iff` / 定理 `mul_and_mul_iff`

English:
theorem mul_and_mul_iff
  given: [Mul R] [IsScalarTower R R M]
  proof: by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact ⟨ba.of_mul, ab.of_mul⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

中文:
定理 mul_and_mul_iff
  条件: [乘法 R] [标量塔 R R M]
  证明: by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact ⟨ba.of_mul, ab.of_mul⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

Depends on / 依赖: ab.of_mul, ba.of_mul, ha.mul, hb.mul, of_mul
-/
theorem mul_and_mul_iff [Mul R] [IsScalarTower R R M] :
    IsSMulRegular M (a * b) ∧ IsSMulRegular M (b * a) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, ba⟩
    exact ⟨ba.of_mul, ab.of_mul⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.mul hb, hb.mul ha⟩

end SMul

section Monoid

variable [Monoid R] [MulAction R M]
variable (M)

/-- One is always `M`-regular. -/
@[simp]
/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: IsSMulRegular M (1 : R)
  proof: fun a b ab => by
  dsimp only [Function.comp_def] at ab
  rw [one_smul]; rw [one_smul] at ab
  assumption

中文:
定理 one
  结论: IsSMulRegular M (1 : R)
  证明: fun a b ab => by
  dsimp only [Function.comp_def] at ab
  rw [one_smul]; rw [one_smul] at ab
  assumption

Depends on / 依赖: Function, Function.comp_def, comp_def, one_smul
-/
theorem one : IsSMulRegular M (1 : R) := fun a b ab => by
  dsimp only [Function.comp_def] at ab
  rw [one_smul]; rw [one_smul] at ab
  assumption

variable {M}

/--
theorem `of_mul_eq_one` / 定理 `of_mul_eq_one`

English:
theorem of_mul_eq_one
  given: (h : a * b = 1)
  statement: IsSMulRegular M b
  proof: of_mul (a := a) (by rw [h]; exact one M)

中文:
定理 of_mul_eq_one
  条件: (h : a * b = 1)
  结论: IsSMulRegular M b
  证明: of_mul (a := a) (by rw [h]; exact one M)

Depends on / 依赖: of_mul
-/
theorem of_mul_eq_one (h : a * b = 1) : IsSMulRegular M b :=
  of_mul (a := a) (by rw [h]; exact one M)

/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: (n : Nat) (ra : IsSMulRegular M a)
  statement: IsSMulRegular M (a ^ n)
  proof: by
  induction n with
  | zero => rw [pow_zero]; simp only [one]
  | succ n hn =>
    rw [pow_succ']
    exact (ra.smul_iff (a ^ n)).mpr hn

中文:
定理 pow
  条件: (n : 自然数) (ra : IsSMulRegular M a)
  结论: IsSMulRegular M (a ^ n)
  证明: by
  induction n with
  | zero => rw [pow_zero]; simp only [one]
  | succ n hn =>
    rw [pow_succ']
    exact (ra.smul_iff (a ^ n)).mpr hn

Depends on / 依赖: pow_succ, pow_zero, ra.smul_iff, smul_iff
-/
theorem pow (n : Nat) (ra : IsSMulRegular M a) : IsSMulRegular M (a ^ n) := by
  induction n with
  | zero => rw [pow_zero]; simp only [one]
  | succ n hn =>
    rw [pow_succ']
    exact (ra.smul_iff (a ^ n)).mpr hn

/--
theorem `pow_iff` / 定理 `pow_iff`

English:
theorem pow_iff
  given: {n : Nat} (n0 : 0 < n)
  statement: IsSMulRegular M (a ^ n) ↔ IsSMulRegular M a
  proof: by
  refine ⟨?_, pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0]; rw [pow_succ]; rw [← smul_eq_mul]
  exact of_smul _

中文:
定理 pow_iff
  条件: {n : 自然数} (n0 : 0 < n)
  结论: IsSMulRegular M (a ^ n) ↔ IsSMulRegular M a
  证明: by
  refine ⟨?_, pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0]; rw [pow_succ]; rw [← smul_eq_mul]
  exact of_smul _

Depends on / 依赖: Nat.succ_pred_eq_of_pos, of_smul, pow_succ, smul_eq_mul, succ_pred_eq_of_pos
-/
theorem pow_iff {n : Nat} (n0 : 0 < n) : IsSMulRegular M (a ^ n) ↔ IsSMulRegular M a := by
  refine ⟨?_, pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0]; rw [pow_succ]; rw [← smul_eq_mul]
  exact of_smul _

end Monoid

section MonoidSMul

variable [Monoid S] [SMul R M] [SMul R S] [MulAction S M] [IsScalarTower R S M]

/--
theorem `of_smul_eq_one` / 定理 `of_smul_eq_one`

English:
theorem of_smul_eq_one
  given: (h : a • s = 1)
  statement: IsSMulRegular M s
  proof: of_smul a
    (by
      rw [h]
      exact one M)

中文:
定理 of_smul_eq_one
  条件: (h : a • s = 1)
  结论: IsSMulRegular M s
  证明: of_smul a
    (by
      rw [h]
      exact one M)

Depends on / 依赖: of_smul
-/
theorem of_smul_eq_one (h : a • s = 1) : IsSMulRegular M s :=
  of_smul a
    (by
      rw [h]
      exact one M)

end MonoidSMul

section MonoidWithZero

variable [MonoidWithZero R] [Zero M] [MulActionWithZero R M]

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: (h : IsSMulRegular M (0 : R))
  statement: Subsingleton M
  proof: ⟨fun a b => h (by dsimp only [Function.comp_def]; repeat' rw [MulActionWithZero.zero_smul])⟩

中文:
定理 subsingleton
  条件: (h : IsSMulRegular M (0 : R))
  结论: 子单例 M
  证明: ⟨fun a b => h (by dsimp only [Function.comp_def]; repeat' rw [MulActionWithZero.zero_smul])⟩
-/
protected theorem subsingleton (h : IsSMulRegular M (0 : R)) : Subsingleton M :=
  ⟨fun a b => h (by dsimp only [Function.comp_def]; repeat' rw [MulActionWithZero.zero_smul])⟩

/--
theorem `zero_iff_subsingleton` / 定理 `zero_iff_subsingleton`

English:
theorem zero_iff_subsingleton
  statement: IsSMulRegular M (0 : R) ↔ Subsingleton M
  proof: ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

中文:
定理 zero_iff_subsingleton
  结论: IsSMulRegular M (0 : R) ↔ 子单例 M
  证明: ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, h.subsingleton, subsingleton
-/
theorem zero_iff_subsingleton : IsSMulRegular M (0 : R) ↔ Subsingleton M :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/--
theorem `not_zero_iff` / 定理 `not_zero_iff`

English:
theorem not_zero_iff
  statement: ¬IsSMulRegular M (0 : R) ↔ Nontrivial M
  proof: by
  rw [nontrivial_iff]; rw [not_iff_comm]; rw [zero_iff_subsingleton]; rw [subsingleton_iff]
  push Not
  exact Iff.rfl

中文:
定理 not_zero_iff
  结论: ¬IsSMulRegular M (0 : R) ↔ 非平凡 M
  证明: by
  rw [nontrivial_iff]; rw [not_iff_comm]; rw [zero_iff_subsingleton]; rw [subsingleton_iff]
  push Not
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, nontrivial_iff, not_iff_comm, subsingleton_iff, zero_iff_subsingleton
-/
theorem not_zero_iff : ¬IsSMulRegular M (0 : R) ↔ Nontrivial M := by
  rw [nontrivial_iff]; rw [not_iff_comm]; rw [zero_iff_subsingleton]; rw [subsingleton_iff]
  push Not
  exact Iff.rfl

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  given: [sM : Subsingleton M]
  statement: IsSMulRegular M (0 : R)
  proof: zero_iff_subsingleton.mpr sM

中文:
定理 zero
  条件: [sM : 子单例 M]
  结论: IsSMulRegular M (0 : R)
  证明: zero_iff_subsingleton.mpr sM

Depends on / 依赖: zero_iff_subsingleton, zero_iff_subsingleton.mpr
-/
theorem zero [sM : Subsingleton M] : IsSMulRegular M (0 : R) :=
  zero_iff_subsingleton.mpr sM

/--
theorem `not_zero` / 定理 `not_zero`

English:
theorem not_zero
  given: [nM : Nontrivial M]
  statement: ¬IsSMulRegular M (0 : R)
  proof: not_zero_iff.mpr nM

中文:
定理 not_zero
  条件: [nM : 非平凡 M]
  结论: ¬IsSMulRegular M (0 : R)
  证明: not_zero_iff.mpr nM

Depends on / 依赖: not_zero_iff, not_zero_iff.mpr
-/
theorem not_zero [nM : Nontrivial M] : ¬IsSMulRegular M (0 : R) :=
  not_zero_iff.mpr nM

end MonoidWithZero

section CommSemigroup

variable [CommSemigroup R] [SMul R M] [IsScalarTower R R M]

/--
theorem `mul_iff` / 定理 `mul_iff`

English:
theorem mul_iff
  statement: IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b
  proof: by
  rw [← mul_and_mul_iff]
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

中文:
定理 mul_iff
  结论: IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b
  证明: by
  rw [← mul_and_mul_iff]
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

Depends on / 依赖: mul_and_mul_iff, mul_comm
-/
theorem mul_iff : IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  rw [← mul_and_mul_iff]
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

end CommSemigroup

end IsSMulRegular

section Group

variable {G : Type*} [Group G]

/--
theorem `isSMulRegular_of_group` / 定理 `isSMulRegular_of_group`

English:
theorem isSMulRegular_of_group
  given: [MulAction G R] (g : G)
  statement: IsSMulRegular R g
  proof: by
  intro x y h
  convert congr_arg (g⁻¹ • ·) h <;> simp [← smul_assoc]

中文:
定理 isSMulRegular_of_group
  条件: [乘法作用 G R] (g : G)
  结论: IsSMulRegular R g
  证明: by
  intro x y h
  convert congr_arg (g⁻¹ • ·) h <;> simp [← smul_assoc]

Depends on / 依赖: congr_arg, convert, smul_assoc
-/
theorem isSMulRegular_of_group [MulAction G R] (g : G) : IsSMulRegular R g := by
  intro x y h
  convert congr_arg (g⁻¹ • ·) h <;> simp [← smul_assoc]

end Group

section Units

variable (M) [Monoid R] [MulAction R M]

/--
theorem `Units.isSMulRegular` / 定理 `Units.isSMulRegular`

English:
theorem Units.isSMulRegular
  given: (a : Rˣ)
  statement: IsSMulRegular M (a : R)
  proof: IsSMulRegular.of_mul_eq_one a.inv_val

中文:
定理 单位群.isSMulRegular
  条件: (a : Rˣ)
  结论: IsSMulRegular M (a : R)
  证明: IsSMulRegular.of_mul_eq_one a.inv_val

Depends on / 依赖: IsSMulRegular, IsSMulRegular.of_mul_eq_one, a.inv_val, inv_val, of_mul_eq_one
-/
theorem Units.isSMulRegular (a : Rˣ) : IsSMulRegular M (a : R) :=
  IsSMulRegular.of_mul_eq_one a.inv_val

/--
theorem `IsUnit.isSMulRegular` / 定理 `IsUnit.isSMulRegular`

English:
theorem IsUnit.isSMulRegular
  given: (ua : IsUnit a)
  statement: IsSMulRegular M a
  proof: by
  rcases ua with ⟨a, rfl⟩
  exact a.isSMulRegular M

中文:
定理 是单位.isSMulRegular
  条件: (ua : 是单位 a)
  结论: IsSMulRegular M a
  证明: by
  rcases ua with ⟨a, rfl⟩
  exact a.isSMulRegular M

Depends on / 依赖: a.isSMulRegular, isSMulRegular
-/
theorem IsUnit.isSMulRegular (ua : IsUnit a) : IsSMulRegular M a := by
  rcases ua with ⟨a, rfl⟩
  exact a.isSMulRegular M

end Units

section SMulZeroClass

/--
lemma `IsSMulRegular.right_eq_zero_of_smul` / 引理 `IsSMulRegular.right_eq_zero_of_smul`

English:
lemma IsSMulRegular.right_eq_zero_of_smul
  statement: [Zero M] [SMulZeroClass R M]
  proof: h1 (h2.trans (smul_zero r).symm)

中文:
引理 IsSMulRegular.right_eq_zero_of_smul
  结论: [零 M] [SMulZero类 R M]
  证明: h1 (h2.trans (smul_zero r).symm)
-/
protected lemma IsSMulRegular.right_eq_zero_of_smul [Zero M] [SMulZeroClass R M]
    {r : R} {x : M} (h1 : IsSMulRegular M r) (h2 : r • x = 0) : x = 0 :=
  h1 (h2.trans (smul_zero r).symm)

end SMulZeroClass

/--
lemma `isSMulRegular_iff_right_eq_zero_of_smul` / 引理 `isSMulRegular_iff_right_eq_zero_of_smul`

English:
lemma isSMulRegular_iff_right_eq_zero_of_smul
  given: [AddGroup M] [DistribSMul R M] {r : R}
  proof: h.right_eq_zero_of_smul
mpr h m₁ m₂ eq := sub_eq_zero.mp h _ by simp_rw [smul_sub, eq, sub_self]

alias ⟨_, IsSMulRegular.of_right_eq_zero_of_smul⟩ := isSMulRegular_iff_right_eq_zero_of_smul

中文:
引理 isSMulRegular_iff_right_eq_zero_of_smul
  条件: [加法群 M] [分配标量乘法 R M] {r : R}
  证明: h.right_eq_zero_of_smul
mpr h m₁ m₂ eq := sub_eq_zero.mp h _ by simp_rw [smul_sub, eq, sub_self]

alias ⟨_, IsSMulRegular.of_right_eq_zero_of_smul⟩ := isSMulRegular_iff_right_eq_zero_of_smul

Depends on / 依赖: h.right_eq_zero_of_smul, right_eq_zero_of_smul
-/
lemma isSMulRegular_iff_right_eq_zero_of_smul [AddGroup M] [DistribSMul R M] {r : R} :
    IsSMulRegular M r ↔ forall m : M, r • m = 0 -> m = 0 where
  mp h _ := h.right_eq_zero_of_smul
mpr h m₁ m₂ eq := sub_eq_zero.mp h _ by simp_rw [smul_sub, eq, sub_self]

alias ⟨_, IsSMulRegular.of_right_eq_zero_of_smul⟩ := isSMulRegular_iff_right_eq_zero_of_smul

/--
lemma `Equiv.isSMulRegular_congr` / 引理 `Equiv.isSMulRegular_congr`

English:
lemma Equiv.isSMulRegular_congr
  statement: {R S M M'} [SMul R M] [SMul S M'] {e : M ≃ M'}
  proof: (e.comp_injective _).symm.trans
(iff_of_eq <| congrArg _ <| funext h).trans e.injective_comp _

中文:
引理 等价.isSMulRegular_congr
  结论: {R S M M'} [标量乘法 R M] [标量乘法 S M'] {e : M ≃ M'}
  证明: (e.comp_injective _).symm.trans
(iff_of_eq <| congrArg _ <| funext h).trans e.injective_comp _

Depends on / 依赖: comp_injective, e.comp_injective, e.injective_comp, iff_of_eq, injective_comp, symm.trans
-/
lemma Equiv.isSMulRegular_congr {R S M M'} [SMul R M] [SMul S M'] {e : M ≃ M'}
    {r : R} {s : S} (h : forall x, e (r • x) = s • e x) :
    IsSMulRegular M r ↔ IsSMulRegular M' s :=
(e.comp_injective _).symm.trans
(iff_of_eq <| congrArg _ <| funext h).trans e.injective_comp _
