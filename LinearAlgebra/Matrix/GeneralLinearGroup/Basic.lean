/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Basic lemmas about the general linear group $GL(n, R)$

This file lists various basic lemmas about the general linear group $GL(n, R)$. For the definitions,
see `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`.
-/

@[expose] public section

namespace Matrix

section Examples

/-- The matrix $[a, -b; b, a]$ (inspired by multiplication by a complex number); it is an element of
$GL_2(R)$ if `a ^ 2 + b ^ 2` is nonzero. -/
@[simps! -fullyApplied val]
/-
**Matrix.planeConformalMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 != 0) : 
Matrix.GeneralLinearGroup (Fin 2) R
参数：a b : R；hab : a ^ 2 + b ^ 2 != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matrix $[a, -b; b, a]$ (inspired by multiplication by a complex number); it 
is an element of
$GL_2(R)$ if `a ^ 2 + b ^ 2` is nonzero.
-/
def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)

/- TODO: Add Iwasawa matrices `n_x=!![1,x; 0,1]`, `a_t=!![exp(t/2),0;0,exp(-t/2)]` and
  `k_θ=!![cos θ, sin θ; -sin θ, cos θ]`
-/
end Examples

namespace GeneralLinearGroup

section Center

variable {R n : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The center of `GL n R` consists of scalar matrices. -/
/-
**Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar** 是 Mathlib 中的一个
引理，位于命名空间 `Matrix.GeneralLinearGroup`。
形式化陈述：mem_center_iff_val_mem_range_scalar {g : GL n R} : g in Subgroup.center (G
L n R) ↔ g.val in Set.range (Matrix.scalar n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mem_range_scalar_of_commute_transvectionStruct`：∀ {n : Type u_1} 
{R : Type u₂} [inst : DecidableEq n] [inst_1 : CommRing R] [inst_2 : Fintype n] 
{M : Matrix n n R},   (∀ (t : Matrix.Transv…
· 使用定理 `Matrix.TransvectionStruct.mul_inv`：mul_inv (t : TransvectionStruct n R) 
: t.toMatrix * t.inv.toMatrix = 1
· 使用定理 `Matrix.TransvectionStruct.inv_mul`：inv_mul (t : TransvectionStruct n R) 
: t.inv.toMatrix * t.toMatrix = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.scalar_comm`：scalar_comm (r : α) (hr : forall r', Commute r r') (
M : Matrix m n α) : scalar m r * M = M * scalar n r
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The center of `GL n R` consists of scalar matrices.
-/
lemma mem_center_iff_val_mem_range_scalar {g : GL n R} :
    g ∈ Subgroup.center (GL n R) ↔ g.val ∈ Set.range (Matrix.scalar n) := by
  constructor
  · intro hg
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t ↦ ?_
    simpa [Units.ext_iff] using! Subgroup.mem_center_iff.mp hg (.mk _ _ t.mul_inv t.inv_mul)
  · refine fun ⟨a, ha⟩ ↦ Subgroup.mem_center_iff.mpr fun h ↦ ?_
    simp [-scalar_apply, Units.ext_iff, ← ha, Matrix.scalar_comm a (Commute.all _)]

@[deprecated (since := "2026-02-08")]
alias mem_center_iff_val_eq_scalar := mem_center_iff_val_mem_range_scalar

/-- The center of `GL n R` is the image of `Rˣ`. -/
/-
**Matrix.GeneralLinearGroup.center_eq_range_scalar** 是 Mathlib 中的一个引理，位于命名空间 `Ma
trix.GeneralLinearGroup`。
形式化陈述：center_eq_range_scalar : Subgroup.center (GL n R) = (scalar n).range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar`：mem_cente
r_iff_val_mem_range_scalar {g : GL n R} : g in Subgroup.center (GL n R) ↔ g.val 
in Set.range (Matrix.scalar n)
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.diagonal_mul_diagonal`：diagonal_mul_diagonal [Fintype n] [Decidab
leEq n] (d₁ d₂ : n -> α) : diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * 
d₂ i
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
The center of `GL n R` is the image of `Rˣ`.
-/
lemma center_eq_range_scalar :
    Subgroup.center (GL n R) = (scalar n).range := by
  ext g
  constructor
  · -- previous lemma shows the underlying matrix is scalar, but now need to show
    -- the scalar is a unit; so we apply argument both to `g` and `g⁻¹`
    intro hg
    cases isEmpty_or_nonempty n with
    | inl hn => simp [nontriviality]
    | inr hn =>
      obtain ⟨a, ha⟩ := mem_center_iff_val_mem_range_scalar.mp hg
      obtain ⟨b, hb⟩ := mem_center_iff_val_mem_range_scalar.mp (Subgroup.inv_mem _ hg)
      have hab : a * b = 1 := by
        simpa [-mul_inv_cancel, ← ha, ← hb, ← diagonal_one, Units.ext_iff] using mul_inv_cancel g
      refine ⟨⟨a, b, hab, mul_comm a b ▸ hab⟩, ?_⟩
      simp [Units.ext_iff, ← ha]
  · rintro ⟨a, rfl⟩
    exact mem_center_iff_val_mem_range_scalar.mpr ⟨a, rfl⟩

@[deprecated (since := "2026-02-08")]
alias center_eq_range_units := center_eq_range_scalar
/-
**Matrix.GeneralLinearGroup.map_center_le** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Gene
ralLinearGroup`。
形式化陈述：map_center_le {S : Type*} [CommRing S] (f : R ->+* S) : Subgroup.center (G
L n R) <= (Subgroup.center (GL n S)).comap (map f)
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.GeneralLinearGroup.center_eq_range_scalar`：center_eq_range_scalar
 : Subgroup.center (GL n R) = (scalar n).range
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.GeneralLinearGroup.map_scalar`：map_scalar (u : Rˣ) : map f (scala
r n u) = scalar n (Units.map f u)
-/
lemma map_center_le {S : Type*} [CommRing S] (f : R →+* S) :
    Subgroup.center (GL n R) ≤ (Subgroup.center (GL n S)).comap (map f) := fun u hu ↦ by
  simp only [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range,
    Subgroup.mem_comap] at hu ⊢
  obtain ⟨r, rfl⟩ := hu
  exact ⟨(Units.map f) r, GeneralLinearGroup.map_scalar _ _ |>.symm⟩

end Center

end GeneralLinearGroup

/-
**Matrix.SpecialLinearGroup.toGL_mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x.SpecialLinearGroup`。
形式化陈述：∀ {n : Type u_1} {R : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommRing R]   (g : Matrix.SpecialLinearGroup n R),   Matrix.SpecialL
inearGroup.toGL g ∈ Subgroup.center (GL n R) ↔ g ∈ Subgroup.center (Matrix.Speci
alLinearGroup n R)
参数：g : Matrix.SpecialLinearGroup n R；GL n R；Matrix.SpecialLinearGroup n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.center_eq_top`：center_eq_top [hG : IsMulCommutative G] : center
 G = ⊤
· 使用定理 `isCyclic_of_subsingleton`：∀ {α : Type u_1} [inst : Group α] [Subsingleto
n α], IsCyclic α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Matrix.GeneralLinearGroup.center_eq_range_scalar`：center_eq_range_scalar
 : Subgroup.center (GL n R) = (scalar n).range
· 使用定理 `Matrix.GeneralLinearGroup.det_scalar`：det_scalar (u : Rˣ) : det (scalar 
n u) = u ^ Fintype.card n
· 使用定理 `Matrix.SpecialLinearGroup.coeToGL_det`：coeToGL_det (g : SpecialLinearGro
up n R) : Matrix.GeneralLinearGroup.det (g : GL n R) = 1
· 使用定理 `Matrix.adjugate.congr_simp`：∀ {n : Type v} {α : Type w} {inst : Decidabl
eEq n} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [inst_3 : CommRing α]   (A 
A_1 : Matrix n n…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.adjugate_diagonal`：adjugate_diagonal (v : n -> α) : adjugate (dia
gonal v) = diagonal fun i => ∏ j in Finset.univ.erase i, v j
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.mul_diagonal`：mul_diagonal [Fintype n] [DecidableEq n] (d : n -> 
α) (M : Matrix m n α) (i j) : (M * diagonal d) i j = M i j * d j
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma SpecialLinearGroup.toGL_mem_center_iff {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (g : SpecialLinearGroup n R) :
    toGL g ∈ Subgroup.center (GL n R) ↔ g ∈ Subgroup.center (SpecialLinearGroup n R) := by
  if hn : IsEmpty n then simp [Subgroup.center_eq_top] else
  replace hn : Nonempty n := by simpa using hn
  obtain ⟨i⟩ := hn
  simp only [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range,
    mem_center_iff, scalar_apply]
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r, by simpa [Units.ext_iff] using congr(GeneralLinearGroup.det $hr),
    by simpa [Units.ext_iff] using hr⟩, fun ⟨r, hr1, hr⟩ ↦ ⟨⟨r, g⁻¹.1 i i, ?_, ?_⟩,
      by simp [Units.ext_iff, hr]⟩⟩
  · simpa [-mul_inv_cancel, ← hr, ← pow_succ',
      Nat.sub_one_add_one Fintype.card_pos.ne.symm] using
        Matrix.ext_iff.2 (Subtype.ext_iff.1 (mul_inv_cancel g)) i i
  · simpa [-inv_mul_cancel, ← hr] using Matrix.ext_iff.2 (Subtype.ext_iff.1 (inv_mul_cancel g)) i i

end Matrix

