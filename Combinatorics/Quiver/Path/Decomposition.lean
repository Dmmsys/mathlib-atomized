/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.Quiver.Path

/-!
# Path Decomposition and Boundary Crossing

This section provides lemmas for decomposing non-empty paths and for reasoning about paths that
cross the boundary of a given set of vertices `S`.
-/

public section
namespace Quiver.Path

section BoundaryEdges

variable {V : Type*} [Quiver V]

/-- A path from a vertex not in `S` to a vertex in `S` must cross the boundary. -/
/-
**Quiver.Path.exists_notMem_mem_hom_path_path_of_notMem_mem** 是 Mathlib 中的一个定理，位
于命名空间 `Quiver.Path`。
形式化陈述：exists_notMem_mem_hom_path_path_of_notMem_mem {a b : V} (p : Path a b) (S 
: Set V) (ha_not_in_S : a ∉ S) (hb_in_S : b in S) : existsᵉ (u ∉ S) (v in S) (e 
: u ⟶ v) (p₁ : Path a u) (p₂ : Path v b), p = p₁.comp (e.toPath.comp p₂)
参数：p : Path a b；S : Set V；ha_not_in_S : a ∉ S；hb_in_S : b in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Path.eq_of_length_zero`：eq_of_length_zero (p : Path a b) (hzero :
 p.length = 0) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Quiver.Path.length_ne_zero_iff_eq_cons`：length_ne_zero_iff_eq_cons : p.l
ength != 0 ↔ exists (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A path from a vertex not in `S` to a vertex in `S` must cross the boundary.
-/
theorem exists_notMem_mem_hom_path_path_of_notMem_mem {a b : V} (p : Path a b) (S : Set V)
    (ha_not_in_S : a ∉ S) (hb_in_S : b ∈ S) :
    ∃ᵉ (u ∉ S) (v ∈ S) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      p = p₁.comp (e.toPath.comp p₂) := by
  induction h_len : p.length generalizing a b S ha_not_in_S hb_in_S with
  | zero =>
    obtain rfl := eq_of_length_zero p h_len
    exact (ha_not_in_S hb_in_S).elim
  | succ n ih =>
    have h_pos : 0 < p.length := by simp [h_len]
    obtain ⟨c, p', e, rfl⟩ := (length_ne_zero_iff_eq_cons p).mp h_pos.ne'
    by_cases hc_in_S : c ∈ S
    · have p'_len : p'.length = n := by simp_all
      obtain ⟨u, hu_not_S, v, hv_S, e_uv, p₁, p₂, hp'⟩ :=
        ih p' S ha_not_in_S hc_in_S p'_len
      refine ⟨u, hu_not_S, v, hv_S, e_uv, p₁, p₂.comp e.toPath, ?_⟩
      simp [hp', comp_toPath_eq_cons]
    · refine ⟨c, hc_in_S, b, hb_in_S, e, p', Path.nil, ?_⟩
      simp [comp_toPath_eq_cons]
/-
**Quiver.Path.exists_mem_notMem_hom_path_path_of_notMem_mem** 是 Mathlib 中的一个定理，位
于命名空间 `Quiver.Path`。
形式化陈述：exists_mem_notMem_hom_path_path_of_notMem_mem {a b : V} (p : Path a b) (S 
: Set V) (ha_in_S : a in S) (hb_not_in_S : b ∉ S) : existsᵉ (u in S) (v ∉ S) (e 
: u ⟶ v) (p₁ : Path a u) (p₂ : Path v b), p = p₁.comp (e.toPath.comp p₂)
参数：p : Path a b；S : Set V；ha_in_S : a in S；hb_not_in_S : b ∉ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.exists_notMem_mem_hom_path_path_of_notMem_mem`：exists_notMem
_mem_hom_path_path_of_notMem_mem {a b : V} (p : Path a b) (S : Set V) (ha_not_in
_S : a ∉ S) (hb_in_S : b in S) : existsᵉ (u ∉ S…
-/
theorem exists_mem_notMem_hom_path_path_of_notMem_mem {a b : V} (p : Path a b) (S : Set V)
    (ha_in_S : a ∈ S) (hb_not_in_S : b ∉ S) :
    ∃ᵉ (u ∈ S) (v ∉ S) (e : u ⟶ v) (p₁ : Path a u) (p₂ : Path v b),
      p = p₁.comp (e.toPath.comp p₂) := by
  have ha_not_in_compl : a ∉ Sᶜ := by simpa
  have hb_in_compl : b ∈ Sᶜ := by simpa
  obtain ⟨u, hu_not_in_compl, v, hv_in_compl, e, p₁, p₂, hp⟩ :=
    exists_notMem_mem_hom_path_path_of_notMem_mem p Sᶜ ha_not_in_compl hb_in_compl
  simp only [Set.mem_compl_iff, not_not] at hu_not_in_compl hv_in_compl
  refine ⟨u, hu_not_in_compl, v, hv_in_compl, e, p₁, p₂, hp⟩

end BoundaryEdges

end Quiver.Path

