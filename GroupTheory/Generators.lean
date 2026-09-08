/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Group generators as data

## Main definitions

* `Group.Generators G ι`: The generators of a group are given by a generating family indexed by `ι`
and an assignment `val : ι → G` such that `Subgroup.closure (Set.range val) = ⊤`.

## Main results

* `Group.Generators.hom_ext`: if two homomorphisms coincide on the elements of a generating family,
  then they are equal.
* `Group.fg_iff_nonempty_finite_generators`: a group is finitely generated if and only if it
  admits a finite generating family.

## Implementation notes

* The index type `ι` is a parameter, not a field, following the pattern of `Algebra.Generators`.
* Unlike `Algebra.Generators`, this structure bundles no section of `FreeGroup.lift val`,
  it just bundles a proof of surjectivity.

## References

* [D. F. Holt, S. Rees, C. E. Röver, *Groups, Languages and Automata*][HoltReesRover2017], §1

## Tags

group generators, generating set, finitely generated
-/

@[expose] public section

variable {G H ι ι' : Type*} [Group G] [Group H]

/-- The generators of a group are given by a generating family indexed by `ι` and an assignment
`val : ι → G` such that `Subgroup.closure (Set.range val) = ⊤`. -/
/-
**Group.Generators** 是 Mathlib 中的一个归纳类型，位于命名空间 `Group`。
形式化陈述：(G : Type u_5) → [Group G] → Type u_6 → Type (max u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generators of a group are given by a generating family indexed by `ι` and an
 assignment
`val : ι → G` such that `Subgroup.closure (Set.range val) = ⊤`.
-/
structure Group.Generators (G : Type*) [Group G] (ι : Type*) where
  /-- The generating family itself: `val i` is the element of `G` indexed by `i : ι`. -/
  val : ι → G
  /-- The subgroup closure of the generators is the whole group. -/
  closure_eq_top : Subgroup.closure (Set.range val) = ⊤

namespace Group.Generators

variable (P : Group.Generators G ι)

/-
**Group.Generators.lift_val_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Group.Generato
rs`。
形式化陈述：lift_val_surjective : Function.Surjective (FreeGroup.lift P.val)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FreeGroup.lift_surjective_iff_closure_range_eq_top`：lift_surjective_iff_
closure_range_eq_top : Function.Surjective (lift f) ↔ Subgroup.closure (Set.rang
e f) = ⊤
· 使用定理 `Group.Generators.closure_eq_top`：∀ {G : Type u_5} [inst : Group G] {ι : 
Type u_6} (self : Group.Generators G ι),   Subgroup.closure (Set.range self.val)
 = ⊤
-/
theorem lift_val_surjective : Function.Surjective (FreeGroup.lift P.val) :=
  FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr P.closure_eq_top

/-- If two homomorphisms coincide on the elements of a generating family, then they are equal. -/
/-
**Group.Generators.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Group.Generators`。
形式化陈述：hom_ext {M : Type*} [Monoid M] (f g : G ->* M) (h : forall i, f (P.val i) 
= g (P.val i)) : f = g
参数：f g : G ->* M；h : forall i, f (P.val i) = g (P.val i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.eq_of_eqOn_dense`：eq_of_eqOn_dense {s : Set G} (hs : closure s
 = ⊤) {f g : G ->* M} (h : s.EqOn f g) : f = g
· 使用定理 `Group.Generators.closure_eq_top`：∀ {G : Type u_5} [inst : Group G] {ι : 
Type u_6} (self : Group.Generators G ι),   Subgroup.closure (Set.range self.val)
 = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
If two homomorphisms coincide on the elements of a generating family, then they 
are equal.
-/
theorem hom_ext {M : Type*} [Monoid M] (f g : G →* M) (h : ∀ i, f (P.val i) = g (P.val i)) :
    f = g := MonoidHom.eq_of_eqOn_dense P.closure_eq_top (Set.forall_mem_range.mpr h)

/-- The generating family obtained using a generating set `S : Set G`. -/
/-
**Group.Generators.ofSet** 是 Mathlib 中的一个定义，位于命名空间 `Group.Generators`。
形式化陈述：ofSet {S : Set G} (h : Subgroup.closure S = ⊤) : Group.Generators G S wher
e val
参数：h : Subgroup.closure S = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generating family obtained using a generating set `S : Set G`.
-/
def ofSet {S : Set G} (h : Subgroup.closure S = ⊤) : Group.Generators G S where
  val := Subtype.val
  closure_eq_top := by rwa [Subtype.range_coe]

@[simp]
/-
**Group.Generators.ofSet_val** 是 Mathlib 中的一个引理，位于命名空间 `Group.Generators`。
形式化陈述：ofSet_val {S : Set G} (hS : Subgroup.closure S = ⊤) : (Group.Generators.of
Set hS).val = Subtype.val
参数：hS : Subgroup.closure S = ⊤。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofSet_val {S : Set G} (hS : Subgroup.closure S = ⊤) :
    (Group.Generators.ofSet hS).val = Subtype.val :=
  rfl

/-- The transport of a generating family along a surjective homomorphism. -/
/-
**Group.Generators.map** 是 Mathlib 中的一个定义，位于命名空间 `Group.Generators`。
形式化陈述：{G : Type u_1} →   {H : Type u_2} →     {ι : Type u_3} →       [inst : Gro
up G] →         [inst_1 : Group H] → Group.Generators G ι → (f : G →* H) → Funct
ion.Surjective ⇑f → Group.Generators H ι
参数：f : G →* H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transport of a generating family along a surjective homomorphism.
-/
protected def map (f : G →* H) (hf : Function.Surjective f) : Group.Generators H ι where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, P.closure_eq_top,
      Subgroup.map_top_of_surjective f hf]

@[simp]
/-
**Group.Generators.map_val** 是 Mathlib 中的一个引理，位于命名空间 `Group.Generators`。
形式化陈述：map_val (P : Group.Generators G ι) (f : G ->* H) (hf : Function.Surjective
 f) : (P.map f hf).val = f ∘ P.val
参数：P : Group.Generators G ι；f : G ->* H；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_val (P : Group.Generators G ι) (f : G →* H) (hf : Function.Surjective f) :
    (P.map f hf).val = f ∘ P.val :=
  rfl

/-- The transport of a generating family along an equivalence of index types. -/
/-
**Group.Generators.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Group.Generators`。
形式化陈述：reindex (P : Group.Generators G ι) (e : ι' ≃ ι) : Group.Generators G ι' wh
ere val
参数：P : Group.Generators G ι；e : ι' ≃ ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transport of a generating family along an equivalence of index types.
-/
def reindex (P : Group.Generators G ι) (e : ι' ≃ ι) : Group.Generators G ι' where
  val := P.val ∘ e
  closure_eq_top := by
    rw [Set.range_comp, EquivLike.range_eq_univ, Set.image_univ, P.closure_eq_top]

@[simp]
/-
**Group.Generators.reindex_val** 是 Mathlib 中的一个引理，位于命名空间 `Group.Generators`。
形式化陈述：reindex_val (P : Group.Generators G ι) (e : ι' ≃ ι) : (P.reindex e).val = 
P.val ∘ e
参数：P : Group.Generators G ι；e : ι' ≃ ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reindex_val (P : Group.Generators G ι) (e : ι' ≃ ι) : (P.reindex e).val = P.val ∘ e :=
  rfl

/-- If `G` has a finite generating family, then `G` is finitely generated. -/
/-
**Group.Generators.fg** 是 Mathlib 中的一个定理，位于命名空间 `Group.Generators`。
形式化陈述：fg [Finite ι] (P : Group.Generators G ι) : Group.FG G
参数：P : Group.Generators G ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.fg_of_surjective`：Group.fg_of_surjective {G' : Type*} [Group G'] [
hG : Group.FG G] {f : G ->* G'} (hf : Function.Surjective f) : Group.FG G'
· 使用定理 `instFGFreeGroupOfFinite`：∀ (α : Type u_5) [Finite α], Group.FG (FreeGrou
p α)
· 使用定理 `Group.Generators.lift_val_surjective`：lift_val_surjective : Function.Sur
jective (FreeGroup.lift P.val)

--- 原说明 ---
If `G` has a finite generating family, then `G` is finitely generated.
-/
theorem fg [Finite ι] (P : Group.Generators G ι) : Group.FG G :=
  Group.fg_of_surjective P.lift_val_surjective

end Group.Generators

/-- A group is finitely generated if and only if it admits a finite generating family. -/
/-
**Group.fg_iff_nonempty_finite_generators** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.fg_iff_nonempty_finite_generators : Group.FG G ↔ exists n : Nat, Non
empty (Group.Generators G (Fin n))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Group.Generators.fg`：fg [Finite ι] (P : Group.Generators G ι) : Group.FG
 G
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
A group is finitely generated if and only if it admits a finite generating famil
y.
-/
theorem Group.fg_iff_nonempty_finite_generators :
    Group.FG G ↔ ∃ n : ℕ, Nonempty (Group.Generators G (Fin n)) := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S.card, ⟨(Group.Generators.ofSet hS).reindex S.equivFin.symm⟩⟩
  · rintro ⟨n, ⟨P⟩⟩
    exact P.fg
