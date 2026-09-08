/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Topology.Sets.OpenCover

/-!
# Grothendieck topology on a topological space

Define the Grothendieck topology and the pretopology associated to a topological space, and show
that the pretopology induces the topology.

The covering (pre)sieves on `X` are those for which the union of domains contains `X`.

## Tags

site, Grothendieck topology, space

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We define the two separately, rather than defining the Grothendieck topology as that generated
by the pretopology for the purpose of having nice definitional properties for the sieves.
-/

@[expose] public section


universe u

namespace Opens

variable (T : Type u) [TopologicalSpace T]

open CategoryTheory TopologicalSpace CategoryTheory.Limits

/-- The Grothendieck topology associated to a topological space. -/
/-
**Opens.grothendieckTopology** 是 Mathlib 中的一个定义，位于命名空间 `Opens`。
形式化陈述：grothendieckTopology : GrothendieckTopology (Opens T) where sieves X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck topology associated to a topological space.
-/
def grothendieckTopology : GrothendieckTopology (Opens T) where
  sieves X := {S | ∀ x ∈ X, ∃ (U : Opens T) (f : U ⟶ X), S f ∧ x ∈ U}
  top_mem' _ _ hx := ⟨_, 𝟙 _, trivial, hx⟩
  pullback_stable' X Y S f hf y hy := by
    rcases hf y (f.le hy) with ⟨U, g, hg, hU⟩
    refine ⟨U ⊓ Y, homOfLE inf_le_right, ?_, hU, hy⟩
    apply S.downward_closed hg (homOfLE inf_le_left)
  transitive' X S hS R hR x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩
    exact ⟨_, g ≫ f, hg, hV⟩
/-
**Opens.mem_grothendieckTopology** 是 Mathlib 中的一个引理，位于命名空间 `Opens`。
形式化陈述：mem_grothendieckTopology {U : Opens T} {S : Sieve U} : S in Opens.grothend
ieckTopology T U ↔ forall x in U, exists (V : _) (f : V ⟶ U), S f ∧ x in V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_grothendieckTopology {U : Opens T} {S : Sieve U} :
    S ∈ Opens.grothendieckTopology T U ↔ ∀ x ∈ U, ∃ (V : _) (f : V ⟶ U), S f ∧ x ∈ V := .rfl

/-- The Grothendieck pretopology associated to a topological space. -/
/-
**Opens.pretopology** 是 Mathlib 中的一个定义，位于命名空间 `Opens`。
形式化陈述：pretopology : Pretopology (Opens T) where coverings X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck pretopology associated to a topological space.
-/
def pretopology : Pretopology (Opens T) where
  coverings X := {R | ∀ x ∈ X, ∃ (U : _) (f : U ⟶ X), R f ∧ x ∈ U}
  has_isos _ _ f _ _ hx := ⟨_, _, Presieve.singleton_self _, (inv f).le hx⟩
  pullbacks X Y f S hS x hx := by
    rcases hS _ (f.le hx) with ⟨U, g, hg, hU⟩
    refine ⟨_, _, Presieve.pullbackArrows.mk _ _ hg, ?_⟩
    have : U ⊓ Y ≤ pullback g f :=
      leOfHom (pullback.lift (homOfLE inf_le_left) (homOfLE inf_le_right) rfl)
    apply this ⟨hU, hx⟩
  transitive X S Ti hS hTi x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩

/-- The pretopology associated to a space is the largest pretopology that
generates the Grothendieck topology associated to the space. -/
@[simp]
/-
**Opens.toPretopology_grothendieckTopology** 是 Mathlib 中的一个定理，位于命名空间 `Opens`。
形式化陈述：toPretopology_grothendieckTopology : (Opens.grothendieckTopology T).toPret
opology = Opens.pretopology T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_
orderTop`：∀ {α : Type u} [inst : SemilatticeInf α] [OrderTop α], CategoryTheory.
Limits.HasFiniteLimits α
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R

--- 原说明 ---
The pretopology associated to a space is the largest pretopology that
generates the Grothendieck topology associated to the space.
-/
theorem toPretopology_grothendieckTopology :
    (Opens.grothendieckTopology T).toPretopology = Opens.pretopology T := by
  apply le_antisymm
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, ⟨V, g₁, g₂, hg₂, _⟩, hU⟩
    exact ⟨V, g₂, hg₂, g₁.le hU⟩
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, hf, hU⟩
    exact ⟨U, f, Sieve.le_generate R U _ hf, hU⟩

/-- The pretopology associated to a space induces the Grothendieck topology associated to the space.
-/
@[simp]
/-
**Opens.pretopology_toGrothendieck** 是 Mathlib 中的一个定理，位于命名空间 `Opens`。
形式化陈述：pretopology_toGrothendieck : (Opens.pretopology T).toGrothendieck = Opens.
grothendieckTopology T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_
orderTop`：∀ {α : Type u} [inst : SemilatticeInf α] [OrderTop α], CategoryTheory.
Limits.HasFiniteLimits α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Opens.toPretopology_grothendieckTopology`：toPretopology_grothendieckTopo
logy : (Opens.grothendieckTopology T).toPretopology = Opens.pretopology T
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
The pretopology associated to a space induces the Grothendieck topology associat
ed to the space.
-/
theorem pretopology_toGrothendieck :
    (Opens.pretopology T).toGrothendieck = Opens.grothendieckTopology T := by
  rw [← toPretopology_grothendieckTopology]
  apply (Pretopology.gi (Opens T)).l_u_eq
/-
**Opens.coversTop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Opens`。
形式化陈述：coversTop_iff {ι : Type*} (U : ι -> Opens T) : (grothendieckTopology T).Co
versTop U ↔ IsOpenCover U
参数：U : ι -> Opens T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.coversTop_iff_of_isTerminal`：coversT
op_iff_of_isTerminal (X : C) (hX : IsTerminal X) {I : Type*} (Y : I -> C) : J.Co
versTop Y ↔ Sieve.ofObjects Y X in J X
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.mk.congr_simp`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (sieves sieves_1 : (X : C) → Set (CategoryTh
eory.Sieve X))   (e_sieves : sieves = s…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma coversTop_iff {ι : Type*} (U : ι → Opens T) :
    (grothendieckTopology T).CoversTop U ↔ IsOpenCover U := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ ⊤ isTerminalTop]
  dsimp [Opens.grothendieckTopology]
  simp only [IsOpenCover, eq_top_iff, SetLike.le_def, exists_and_right, Opens.mem_top,
    Opens.mem_iSup, forall_const]
  refine ⟨fun h x ↦ ?_, fun hU x hx ↦ ?_⟩
  · obtain ⟨V, ⟨u, ⟨i, ⟨hi⟩⟩⟩, hx⟩ := h x trivial
    use i, leOfHom hi hx
  · obtain ⟨i, hi⟩ := hU (x := x)
    exact ⟨U i, ⟨homOfLE le_top, ⟨i, ⟨𝟙 _⟩⟩⟩, hi⟩

end Opens

