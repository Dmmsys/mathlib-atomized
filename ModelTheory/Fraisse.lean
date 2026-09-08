/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
module

public import Mathlib.ModelTheory.FinitelyGenerated
public import Mathlib.ModelTheory.PartialEquiv
public import Mathlib.ModelTheory.Bundled
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Fraïssé Classes and Fraïssé Limits

This file pertains to the ages of countable first-order structures. The age of a structure is the
class of all finitely-generated structures that embed into it.

Of particular interest are Fraïssé classes, which are exactly the ages of countable
ultrahomogeneous structures. To each is associated a unique (up to nonunique isomorphism)
Fraïssé limit - the countable ultrahomogeneous structure with that age.

## Main Definitions

- `FirstOrder.Language.age` is the class of finitely-generated structures that embed into a
  particular structure.
- A class `K` is `FirstOrder.Language.Hereditary` when all finitely-generated
  structures that embed into structures in `K` are also in `K`.
- A class `K` has `FirstOrder.Language.JointEmbedding` when for every `M`, `N` in
  `K`, there is another structure in `K` into which both `M` and `N` embed.
- A class `K` has `FirstOrder.Language.Amalgamation` when for any pair of embeddings
  of a structure `M` in `K` into other structures in `K`, those two structures can be embedded into
  a fourth structure in `K` such that the resulting square of embeddings commutes.
- `FirstOrder.Language.IsFraisse` indicates that a class is nonempty, essentially countable,
  and satisfies the hereditary, joint embedding, and amalgamation properties.
- `FirstOrder.Language.IsFraisseLimit` indicates that a structure is a Fraïssé limit for a given
  class.

## Main Results

- We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
  joint-embedding properties.
- `FirstOrder.Language.age.countable_quotient` shows that the age of any countable structure is
  essentially countable.
- `FirstOrder.Language.exists_countable_is_age_of_iff` gives necessary and sufficient conditions
  for a class to be the age of a countable structure in a language with countably many functions.
- `FirstOrder.Language.IsFraisseLimit.nonempty_equiv` shows that any class which is Fraïssé has
  at most one Fraïssé limit up to equivalence.
- `FirstOrder.Language.empty.isFraisseLimit_of_countable_infinite` shows that any countably infinite
  structure in the empty language is a Fraïssé limit of the class of finite structures.
- `FirstOrder.Language.empty.isFraisse_finite` shows that the class of finite structures in the
  empty language is Fraïssé.

## Implementation Notes

- Classes of structures are formalized with `Set (Bundled L.Structure)`.
- Some results pertain to countable limit structures, others to countably-generated limit
  structures. In the case of a language with countably many function symbols, these are equivalent.

## References

- [W. Hodges, *A Shorter Model Theory*][Hodges97]
- [K. Tent, M. Ziegler, *A Course in Model Theory*][Tent_Ziegler]

## TODO

- Show existence of Fraïssé limits

-/

@[expose] public section


universe u v w w'

open scoped FirstOrder

open Set CategoryTheory

namespace FirstOrder

namespace Language

open Structure Substructure

variable (L : Language.{u, v})

/-! ### The Age of a Structure and Fraïssé Classes -/


/-- The age of a structure `M` is the class of finitely-generated structures that embed into it. -/
/-
**FirstOrder.Language.age** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：age (M : Type w) [L.Structure M] : Set (Bundled.{w} L.Structure)
参数：M : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The age of a structure `M` is the class of finitely-generated structures that em
bed into it.
-/
def age (M : Type w) [L.Structure M] : Set (Bundled.{w} L.Structure) :=
  {N | Structure.FG L N ∧ Nonempty (N ↪[L] M)}

variable {L}
variable (K : Set (Bundled.{w} L.Structure))

/-- A class `K` has the hereditary property when all finitely-generated structures that embed into
  structures in `K` are also in `K`. -/
/-
**FirstOrder.Language.Hereditary** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`
。
形式化陈述：Hereditary : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class `K` has the hereditary property when all finitely-generated structures t
hat embed into
  structures in `K` are also in `K`.
-/
def Hereditary : Prop :=
  ∀ M : Bundled.{w} L.Structure, M ∈ K → L.age M ⊆ K

/-- A class `K` has the joint embedding property when for every `M`, `N` in `K`, there is another
/-
**FirstOrder.Language.in** 是 Mathlib 中的一个结构，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
  structure in `K` into which both `M` and `N` embed. -/
/-
**FirstOrder.Language.JointEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：JointEmbedding : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class `K` has the joint embedding property when for every `M`, `N` in `K`, the
re is another
  structure in `K` into which both `M` and `N` embed.
-/
def JointEmbedding : Prop :=
  DirectedOn (fun M N : Bundled.{w} L.Structure => Nonempty (M ↪[L] N)) K

/-- A class `K` has the amalgamation property when for any pair of embeddings of a structure `M` in
  `K` into other structures in `K`, those two structures can be embedded into a fourth structure in
  `K` such that the resulting square of embeddings commutes. -/
/-
**FirstOrder.Language.Amalgamation** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e`。
形式化陈述：Amalgamation : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class `K` has the amalgamation property when for any pair of embeddings of a s
tructure `M` in
  `K` into other structures in `K`, those two structures can be embedded into a 
fourth structure in
  `K` such that the resulting square of embeddings commutes.
-/
def Amalgamation : Prop :=
  ∀ (M N P : Bundled.{w} L.Structure) (MN : M ↪[L] N) (MP : M ↪[L] P),
    M ∈ K → N ∈ K → P ∈ K → ∃ (Q : Bundled.{w} L.Structure) (NQ : N ↪[L] Q) (PQ : P ↪[L] Q),
      Q ∈ K ∧ NQ.comp MN = PQ.comp MP

/-- A Fraïssé class is a nonempty, essentially countable class of structures satisfying the
hereditary, joint embedding, and amalgamation properties. -/
/-
**FirstOrder.Language.IsFraisse** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Language
`。
形式化陈述：{L : FirstOrder.Language} → Set (CategoryTheory.Bundled L.Structure) → Pro
p
参数：CategoryTheory.Bundled L.Structure。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Fraïssé class is a nonempty, essentially countable class of structures satisfy
ing the
hereditary, joint embedding, and amalgamation properties.
-/
class IsFraisse : Prop where
  is_nonempty : K.Nonempty
  FG : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M
  is_essentially_countable : (Quotient.mk' '' K).Countable
  hereditary : Hereditary K
  jointEmbedding : JointEmbedding K
  amalgamation : Amalgamation K

variable {K} (L) (M : Type w) [Structure L M]
/-
**FirstOrder.Language.age.is_equiv_invariant** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.age`。
形式化陈述：∀ (L : FirstOrder.Language) (M : Type w) [inst : L.Structure M] (N P : Cat
egoryTheory.Bundled L.Structure),   Nonempty (L.Equiv ↑N ↑P) → (N ∈ L.age M ↔ P 
∈ L.age M)
参数：L : FirstOrder.Language；M : Type w；N P : CategoryTheory.Bundled L.Structure；L
.Equiv ↑N ↑P；N ∈ L.age M ↔ P ∈ L.age M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `FirstOrder.Language.Equiv.fg_iff`：∀ {L : FirstOrder.Language} {M : Type 
u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N]   (f : L.Equ
iv M N), FirstOrder.La…
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem age.is_equiv_invariant (N P : Bundled.{w} L.Structure) (h : Nonempty (N ≃[L] P)) :
    N ∈ L.age M ↔ P ∈ L.age M :=
  and_congr h.some.fg_iff
    ⟨Nonempty.map fun x => Embedding.comp x h.some.symm.toEmbedding,
      Nonempty.map fun x => Embedding.comp x h.some.toEmbedding⟩

variable {L} {M} {N : Type w} [Structure L N]
/-
**FirstOrder.Language.Embedding.age_subset_age** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Embedding`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {N : Type 
w} [inst_1 : L.Structure N]   (MN : L.Embedding M N), L.age M ⊆ L.age N
参数：MN : L.Embedding M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem Embedding.age_subset_age (MN : M ↪[L] N) : L.age M ⊆ L.age N := fun _ =>
  And.imp_right (Nonempty.map MN.comp)
/-
**FirstOrder.Language.Equiv.age_eq_age** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Equiv`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {N : Type 
w} [inst_1 : L.Structure N]   (MN : L.Equiv M N), L.age M = L.age N
参数：MN : L.Equiv M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `FirstOrder.Language.Embedding.age_subset_age`：∀ {L : FirstOrder.Language
} {M : Type w} [inst : L.Structure M] {N : Type w} [inst_1 : L.Structure N]   (M
N : L.Embedding M N), L.age M ⊆ L.…
-/
theorem Equiv.age_eq_age (MN : M ≃[L] N) : L.age M = L.age N :=
  le_antisymm MN.toEmbedding.age_subset_age MN.symm.toEmbedding.age_subset_age
/-
**FirstOrder.Language.Structure.FG.mem_age_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Structure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M N : CategoryTheory.Bundled L.Structure},   
FirstOrder.Language.Structure.FG L ↑M → Nonempty (L.Equiv ↑M ↑N) → N ∈ L.age ↑M
参数：L.Equiv ↑M ↑N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Equiv.fg_iff`：∀ {L : FirstOrder.Language} {M : Type 
u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N]   (f : L.Equ
iv M N), FirstOrder.La…
-/
theorem Structure.FG.mem_age_of_equiv {M N : Bundled L.Structure} (h : Structure.FG L M)
    (MN : Nonempty (M ≃[L] N)) : N ∈ L.age M :=
  ⟨MN.some.fg_iff.1 h, ⟨MN.some.symm.toEmbedding⟩⟩
/-
**FirstOrder.Language.Hereditary.is_equiv_invariant_of_fg** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.Hereditary`。
形式化陈述：∀ {L : FirstOrder.Language} {K : Set (CategoryTheory.Bundled L.Structure)}
,   FirstOrder.Language.Hereditary K →     (∀ M ∈ K, FirstOrder.Language.Structu
re.FG L ↑M) →       ∀ (M N : CategoryTheory.Bundled L.Structure), Nonempty (L.Eq
uiv ↑M ↑N) → (M ∈ K ↔ N ∈ K)
参数：CategoryTheory.Bundled L.Structure；∀ M ∈ K, FirstOrder.Language.Structure.FG 
L ↑M；M N : CategoryTheory.Bundled L.Structure；L.Equiv ↑M ↑N；M ∈ K ↔ N ∈ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.FG.mem_age_of_equiv`：∀ {L : FirstOrder.Lan
guage} {M N : CategoryTheory.Bundled L.Structure},   FirstOrder.Language.Structu
re.FG L ↑M → Nonempty (L.Equiv ↑M ↑N) →…
-/
theorem Hereditary.is_equiv_invariant_of_fg (h : Hereditary K)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) (M N : Bundled.{w} L.Structure)
    (hn : Nonempty (M ≃[L] N)) : M ∈ K ↔ N ∈ K :=
  ⟨fun MK => h M MK ((fg M MK).mem_age_of_equiv hn),
   fun NK => h N NK ((fg N NK).mem_age_of_equiv ⟨hn.some.symm⟩)⟩
/-
**FirstOrder.Language.IsFraisse.is_equiv_invariant** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.IsFraisse`。
形式化陈述：∀ {L : FirstOrder.Language} {K : Set (CategoryTheory.Bundled L.Structure)}
 [h : FirstOrder.Language.IsFraisse K]   {M N : CategoryTheory.Bundled L.Structu
re}, Nonempty (L.Equiv ↑M ↑N) → (M ∈ K ↔ N ∈ K)
参数：CategoryTheory.Bundled L.Structure；L.Equiv ↑M ↑N；M ∈ K ↔ N ∈ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hereditary.is_equiv_invariant_of_fg`：∀ {L : FirstOrd
er.Language} {K : Set (CategoryTheory.Bundled L.Structure)},   FirstOrder.Langua
ge.Hereditary K →     (∀ M ∈ K, FirstOrder.La…
· 使用定理 `FirstOrder.Language.IsFraisse.hereditary`：∀ {L : FirstOrder.Language} {K
 : Set (CategoryTheory.Bundled L.Structure)} [self : FirstOrder.Language.IsFrais
se K],   FirstOrder.Language.H…
· 使用定理 `FirstOrder.Language.IsFraisse.FG`：∀ {L : FirstOrder.Language} {K : Set (
CategoryTheory.Bundled L.Structure)} [self : FirstOrder.Language.IsFraisse K],  
 ∀ M ∈ K, FirstOrder.L…
-/
theorem IsFraisse.is_equiv_invariant [h : IsFraisse K] {M N : Bundled.{w} L.Structure}
    (hn : Nonempty (M ≃[L] N)) : M ∈ K ↔ N ∈ K :=
  h.hereditary.is_equiv_invariant_of_fg h.FG M N hn

variable (M)
/-
**FirstOrder.Language.age.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Languag
e.age`。
形式化陈述：∀ {L : FirstOrder.Language} (M : Type w) [inst : L.Structure M], (L.age M)
.Nonempty
参数：M : Type w；L.age M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `FirstOrder.Language.Substructure.fg_closure`：fg_closure {s : Set M} (hs 
: s.Finite) : FG (closure L s)
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
-/
theorem age.nonempty : (L.age M).Nonempty :=
  ⟨Bundled.of (Substructure.closure L (∅ : Set M)),
    (fg_iff_structure_fg _).1 (fg_closure Set.finite_empty), ⟨Substructure.subtype _⟩⟩
/-
**FirstOrder.Language.age.hereditary** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.age`。
形式化陈述：∀ {L : FirstOrder.Language} (M : Type w) [inst : L.Structure M], FirstOrde
r.Language.Hereditary (L.age M)
参数：M : Type w；L.age M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.age_subset_age`：∀ {L : FirstOrder.Language
} {M : Type w} [inst : L.Structure M] {N : Type w} [inst_1 : L.Structure N]   (M
N : L.Embedding M N), L.age M ⊆ L.…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem age.hereditary : Hereditary (L.age M) := fun _ hN _ hP => hN.2.some.age_subset_age hP
/-
**FirstOrder.Language.age.jointEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.age`。
形式化陈述：∀ {L : FirstOrder.Language} (M : Type w) [inst : L.Structure M], FirstOrde
r.Language.JointEmbedding (L.age M)
参数：M : Type w；L.age M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `FirstOrder.Language.Substructure.FG.sup`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] {N₁ N₂ : L.Substructure M},   N₁.FG → N₂.FG →
 (N₁ ⊔ N₂).FG
· 使用定理 `FirstOrder.Language.Structure.FG.range`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N],   Fir
stOrder.Language.Structure.F…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem age.jointEmbedding : JointEmbedding (L.age M) := fun _ hN _ hP =>
  ⟨Bundled.of (↥(hN.2.some.toHom.range ⊔ hP.2.some.toHom.range)),
    ⟨(fg_iff_structure_fg _).1 ((hN.1.range hN.2.some.toHom).sup (hP.1.range hP.2.some.toHom)),
      ⟨Substructure.subtype _⟩⟩,
    ⟨Embedding.comp (inclusion le_sup_left) hN.2.some.equivRange.toEmbedding⟩,
    ⟨Embedding.comp (inclusion le_sup_right) hP.2.some.equivRange.toEmbedding⟩⟩

variable {M} in
/-
**FirstOrder.Language.age.fg_substructure** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.age`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {S : L.Sub
structure M},   S.FG → { α := ↥S, str := inferInstance } ∈ L.age M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
-/
theorem age.fg_substructure {S : L.Substructure M} (fg : S.FG) : Bundled.mk S ∈ L.age M := by
  exact ⟨(Substructure.fg_iff_structure_fg _).1 fg, ⟨subtype _⟩⟩

/-- Any class in the age of a structure has a representative which is a finitely generated
substructure. -/
/-
**FirstOrder.Language.age.has_representative_as_substructure** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.age`。
形式化陈述：∀ {L : FirstOrder.Language} (M : Type w) [inst : L.Structure M],   ∀ C ∈ Q
uotient.mk' '' L.age M, ∃ V, ⟦{ α := ↥↑V, str := inferInstance }⟧ = C
参数：M : Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `FirstOrder.Language.Structure.FG.range`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N],   Fir
stOrder.Language.Structure.F…
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Any class in the age of a structure has a representative which is a finitely gen
erated
substructure.
-/
theorem age.has_representative_as_substructure :
    ∀ C ∈ Quotient.mk' '' L.age M, ∃ V : {V : L.Substructure M // FG V},
      ⟦Bundled.mk V⟧ = C := by
  rintro _ ⟨N, ⟨N_fg, ⟨N_incl⟩⟩, N_eq⟩
  refine N_eq.symm ▸ ⟨⟨N_incl.toHom.range, ?_⟩, Quotient.sound ⟨N_incl.equivRange.symm⟩⟩
  exact FG.range N_fg (Embedding.toHom N_incl)

/-- The age of a countable structure is essentially countable (has countably many isomorphism
classes). -/
/-
**FirstOrder.Language.age.countable_quotient** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.age`。
形式化陈述：∀ {L : FirstOrder.Language} (M : Type w) [inst : L.Structure M] [h : Count
able M], (Quotient.mk' '' L.age M).Countable
参数：M : Type w；Quotient.mk' '' L.age M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.forall`：Quotient.forall {α : Sort*} {s : Setoid α} {p : Quotien
t s -> Prop} : (forall a, p a) ↔ forall a : α, p ⟦a⟧
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `FirstOrder.Language.Substructure.fg_closure`：fg_closure {s : Set M} (hs 
: s.Finite) : FG (closure L s)
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Embedding.coe_toHom`：coe_toHom {f : M ↪[L] N} : (f.t
oHom : M -> N) = f
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `FirstOrder.Language.Substructure.closure_image`：closure_image (f : M ->[
L] N) : closure L (f '' s) = map f (closure L s)
· 使用定理 `FirstOrder.Language.Hom.range_eq_map`：range_eq_map (f : M ->[L] N) : f.r
ange = map f ⊤
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)

--- 原说明 ---
The age of a countable structure is essentially countable (has countably many is
omorphism
classes).
-/
theorem age.countable_quotient [h : Countable M] : (Quotient.mk' '' L.age M).Countable := by
  classical
  refine (congr_arg _ (Set.ext <| Quotient.forall.2 fun N => ?_)).mp
    (countable_range fun s : Finset M => ⟦⟨closure L (s : Set M), inferInstance⟩⟧)
  constructor
  · rintro ⟨s, hs⟩
    use Bundled.of (closure L (s : Set M))
    exact ⟨⟨(fg_iff_structure_fg _).1 (fg_closure s.finite_toSet), ⟨Substructure.subtype _⟩⟩, hs⟩
  · simp only [mem_range, Quotient.eq]
    rintro ⟨P, ⟨⟨s, hs⟩, ⟨PM⟩⟩, hP2⟩
    refine ⟨s.image PM, Setoid.trans (b := P) ?_ <| Quotient.exact hP2⟩
    rw [← Embedding.coe_toHom, Finset.coe_image, closure_image PM.toHom, hs, ← Hom.range_eq_map]
    exact ⟨PM.equivRange.symm⟩

set_option backward.isDefEq.respectTransparency false in
-- This is not a simp-lemma because it does not apply to itself.
/-- The age of a direct limit of structures is the union of the ages of the structures. -/
/-
**FirstOrder.Language.age_directLimit** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage`。
形式化陈述：age_directLimit {ι : Type w} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
 (G : ι -> Type max w w') [forall i, L.Structure (G i)] (f : forall i j, i <= j 
-> G i ↪[L] G j) [DirectedSystem G fun i j h => f i j h] : L.age (DirectLimit G 
f) = ⋃ i : ι, L.age (G i)
参数：G : ι -> Type max w w'；G i；f : forall i j, i <= j -> G i ↪[L] G j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Structure.FG.range`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N],   Fir
stOrder.Language.Structure.F…
· 使用定理 `Finset.exists_le`：Finset.exists_le [Nonempty α] [Preorder α] [IsDirected
Order α] (s : Finset α) : exists M, forall i in s, i <= M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Substructure.closure_le`：closure_le : closure L s <=
 S ↔ s subseteq S
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `FirstOrder.Language.Embedding.coe_toHom`：coe_toHom {f : M ↪[L] N} : (f.t
oHom : M -> N) = f
· 使用定理 `FirstOrder.Language.DirectLimit.of_apply`：of_apply {i : ι} {x : G i} : o
f L ι G f i x = ⟦.mk f i x⟧
· 使用定理 `Quotient.mk_eq_iff_out`：Quotient.mk_eq_iff_out {s : Setoid α} {x : α} {y
 : Quotient s} : ⟦x⟧ = y ↔ x ≈ Quotient.out y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `FirstOrder.Language.DirectLimit.equiv_iff`：equiv_iff {x y : Σˣ f} {i : ι
} (hx : x.1 <= i) (hy : y.1 <= i) : x ≈ y ↔ (f x.1 i hx) x.2 = (f y.1 i hy) y.2
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `FirstOrder.Language.DirectedSystem.map_self`：∀ {ι : Type u_1} [inst : Pr
eorder ι] {F : ι → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι)
 → (h : i ≤ j) → T h) [inst_1 : ⦃…

--- 原说明 ---
The age of a direct limit of structures is the union of the ages of the structur
es.
-/
theorem age_directLimit {ι : Type w} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type max w w') [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h => f i j h] : L.age (DirectLimit G f) = ⋃ i : ι, L.age (G i) := by
  classical
  ext M
  simp only [mem_iUnion]
  constructor
  · rintro ⟨Mfg, ⟨e⟩⟩
    obtain ⟨s, hs⟩ := Mfg.range e.toHom
    let out := @Quotient.out _ (DirectLimit.setoid G f)
    obtain ⟨i, hi⟩ := Finset.exists_le (s.image (Sigma.fst ∘ out))
    have e' := (DirectLimit.of L ι G f i).equivRange.symm.toEmbedding
    refine ⟨i, Mfg, ⟨e'.comp ((Substructure.inclusion ?_).comp e.equivRange.toEmbedding)⟩⟩
    rw [← hs, closure_le]
    intro x hx
    refine ⟨f (out x).1 i (hi (out x).1 (Finset.mem_image_of_mem _ hx)) (out x).2, ?_⟩
    rw [Embedding.coe_toHom, DirectLimit.of_apply, @Quotient.mk_eq_iff_out _ (_),
      DirectLimit.equiv_iff G f (le_refl _) (hi (out x).1 (Finset.mem_image_of_mem _ hx)),
      DirectedSystem.map_self]
  · rintro ⟨i, Mfg, ⟨e⟩⟩
    exact ⟨Mfg, ⟨Embedding.comp (DirectLimit.of L ι G f i) e⟩⟩

/-- Sufficient conditions for a class to be the age of a countably-generated structure. -/
/-
**FirstOrder.Language.exists_cg_is_age_of** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language`。
形式化陈述：exists_cg_is_age_of (hn : K.Nonempty) (hc : (Quotient.mk' '' K).Countable)
 (fg : forall M : Bundled.{w} L.Structure, M in K -> Structure.FG L M) (hp : Her
editary K) (jep : JointEmbedding K) : exists M : Bundled.{w} L.Structure, Struct
ure.CG L M ∧ L.age M = K
参数：hn : K.Nonempty；hc : (Quotient.mk' '' K).Countable；fg : forall M : Bundled.{w
} L.Structure, M in K -> Structure.FG L M；hp : Hereditary K；jep : JointEmbedding
 K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Set.Countable.exists_eq_range`：∀ {α : Type u} {s : Set α}, s.Countable →
 s.Nonempty → ∃ f, s = Set.range f
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `Quotient.mk_out`：Quotient.mk_out {s : Setoid α} (a : α) : s (⟦a⟧ : Quoti
ent s).out a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Hereditary.is_equiv_invariant_of_fg`：∀ {L : FirstOrd
er.Language} {K : Set (CategoryTheory.Bundled L.Structure)},   FirstOrder.Langua
ge.Hereditary K →     (∀ M ∈ K, FirstOrder.La…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `FirstOrder.Language.DirectedSystem.natLERec.directedSystem`：∀ {L : First
Order.Language} {G' : ℕ → Type w} [inst : (i : ℕ) → L.Structure (G' i)]   (f' : 
(n : ℕ) → L.Embedding (G' n) (G' (n + 1))),   Di…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `FirstOrder.Language.DirectLimit.cg`：cg {ι : Type*} [Countable ι] [Preord
er ι] [IsDirectedOrder ι] [Nonempty ι] {G : ι -> Type w} [forall i, L.Structure 
(G i)] (f : forall i j, …
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `FirstOrder.Language.Structure.FG.cg`：∀ {L : FirstOrder.Language} {M : Ty
pe u_1} [inst : L.Structure M],   FirstOrder.Language.Structure.FG L M → FirstOr
der.Language.Structure.CG…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `FirstOrder.Language.age_directLimit`：age_directLimit {ι : Type w} [Preor
der ι] [IsDirectedOrder ι] [Nonempty ι] (G : ι -> Type max w w') [forall i, L.St
ructure (G i)] (f : foral…
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Quotient.eq_mk_iff_out`：Quotient.eq_mk_iff_out {s : Setoid α} {x : Quoti
ent s} {y : α} : x = ⟦y⟧ ↔ Quotient.out x ≈ y
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Sufficient conditions for a class to be the age of a countably-generated structu
re.
-/
theorem exists_cg_is_age_of (hn : K.Nonempty)
    (hc : (Quotient.mk' '' K).Countable)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) (hp : Hereditary K)
    (jep : JointEmbedding K) : ∃ M : Bundled.{w} L.Structure, Structure.CG L M ∧ L.age M = K := by
  obtain ⟨F, hF⟩ := hc.exists_eq_range (hn.image _)
  simp only [Set.ext_iff, Quotient.forall, mem_image, mem_range] at hF
  simp_rw [Quotient.eq_mk_iff_out] at hF
  have hF' : ∀ n : ℕ, (F n).out ∈ K := by
    intro n
    obtain ⟨P, hP1, hP2⟩ := (hF (F n).out).2 ⟨n, Setoid.refl _⟩
    -- Porting note: fix hP2 because `Quotient.out (Quotient.mk' x) ≈ a` was not simplified
    -- to `x ≈ a` in hF
    replace hP2 := Setoid.trans (Setoid.symm (Quotient.mk_out P)) hP2
    exact (hp.is_equiv_invariant_of_fg fg _ _ hP2).1 hP1
  choose P hPK hP hFP using fun (N : K) (n : ℕ) => jep N N.2 (F (n + 1)).out (hF' _)
  let G : ℕ → K := @Nat.rec (fun _ => K) ⟨(F 0).out, hF' 0⟩ fun n N => ⟨P N n, hPK N n⟩
  let f : ∀ (i j : ℕ), i ≤ j → (G i).val ↪[L] (G j).val :=
    DirectedSystem.natLERec fun n => (hP _ n).some
  refine ⟨Bundled.of (@DirectLimit L _ _ (fun n ↦ (G n).val) _ f _ _), ?_, ?_⟩
  · exact DirectLimit.cg _ (fun n => (fg _ (G n).2).cg)
  · refine (age_directLimit (fun n ↦ (G n).val) f).trans
      (subset_antisymm (iUnion_subset fun n N hN => hp (G n).val (G n).2 hN) fun N KN => ?_)
    have : Quotient.out (Quotient.mk' N) ≈ N := Quotient.eq_mk_iff_out.mp rfl
    obtain ⟨n, ⟨e⟩⟩ := (hF N).1 ⟨N, KN, this⟩
    refine mem_iUnion_of_mem n ⟨fg _ KN, ⟨Embedding.comp ?_ e.symm.toEmbedding⟩⟩
    rcases n with - | n
    · dsimp [G]; exact Embedding.refl _ _
    · dsimp [G]; exact (hFP _ n).some
/-
**FirstOrder.Language.exists_countable_is_age_of_iff** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language`。
形式化陈述：exists_countable_is_age_of_iff [Countable (Σ l, L.Functions l)] : (exists 
M : Bundled.{w} L.Structure, Countable M ∧ L.age M = K) ↔ K.Nonempty ∧ (forall M
 N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) -> (M in K ↔ N in K)) ∧ (Quoti
ent.mk' '' K).Countable ∧ (forall M : Bundled.{w} L.Structure, M in K -> Structu
re.FG L M) ∧ Hereditary K ∧ JointEmbedding K
参数：Σ l, L.Functions l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `FirstOrder.Language.age.nonempty`：∀ {L : FirstOrder.Language} (M : Type 
w) [inst : L.Structure M], (L.age M).Nonempty
· 使用定理 `FirstOrder.Language.age.is_equiv_invariant`：∀ (L : FirstOrder.Language) 
(M : Type w) [inst : L.Structure M] (N P : CategoryTheory.Bundled L.Structure), 
  Nonempty (L.Equiv ↑N ↑P) → (N …
· 使用定理 `FirstOrder.Language.age.countable_quotient`：∀ {L : FirstOrder.Language} 
(M : Type w) [inst : L.Structure M] [h : Countable M], (Quotient.mk' '' L.age M)
.Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `FirstOrder.Language.age.hereditary`：∀ {L : FirstOrder.Language} (M : Typ
e w) [inst : L.Structure M], FirstOrder.Language.Hereditary (L.age M)
· 使用定理 `FirstOrder.Language.age.jointEmbedding`：∀ {L : FirstOrder.Language} (M :
 Type w) [inst : L.Structure M], FirstOrder.Language.JointEmbedding (L.age M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.exists_cg_is_age_of`：exists_cg_is_age_of (hn : K.Non
empty) (hc : (Quotient.mk' '' K).Countable) (fg : forall M : Bundled.{w} L.Struc
ture, M in K -> Structure.FG …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Structure.cg_iff_countable`：cg_iff_countable [Counta
ble (Σ l, L.Functions l)] : CG L M ↔ Countable M
-/
theorem exists_countable_is_age_of_iff [Countable (Σ l, L.Functions l)] :
    (∃ M : Bundled.{w} L.Structure, Countable M ∧ L.age M = K) ↔
      K.Nonempty ∧ (∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)) ∧
      (Quotient.mk' '' K).Countable ∧ (∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.FG L M) ∧
      Hereditary K ∧ JointEmbedding K := by
  constructor
  · rintro ⟨M, h1, h2, rfl⟩
    refine ⟨age.nonempty M, age.is_equiv_invariant L M, age.countable_quotient M, fun N hN => hN.1,
      age.hereditary M, age.jointEmbedding M⟩
  · rintro ⟨Kn, _, cq, hfg, hp, jep⟩
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn cq hfg hp jep
    exact ⟨M, Structure.cg_iff_countable.1 hM, rfl⟩

variable (L)

/-- A structure `M` is ultrahomogeneous if every embedding of a finitely generated substructure
into `M` extends to an automorphism of `M`. -/
/-
**FirstOrder.Language.IsUltrahomogeneous** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：IsUltrahomogeneous : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure `M` is ultrahomogeneous if every embedding of a finitely generated s
ubstructure
into `M` extends to an automorphism of `M`.
-/
def IsUltrahomogeneous : Prop :=
  ∀ (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] M),
    ∃ g : M ≃[L] M, f = g.toEmbedding.comp S.subtype

variable {L} (K)

/-- A structure `M` is a Fraïssé limit for a class `K` if it is countably generated,
ultrahomogeneous, and has age `K`. -/
/-
**FirstOrder.Language.IsFraisseLimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Lan
guage`。
形式化陈述：{L : FirstOrder.Language} →   Set (CategoryTheory.Bundled L.Structure) →  
   (M : Type w) → [L.Structure M] → [Countable ((l : ℕ) × L.Functions l)] → [Cou
ntable M] → Prop
参数：CategoryTheory.Bundled L.Structure；M : Type w；(l : ℕ) × L.Functions l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure `M` is a Fraïssé limit for a class `K` if it is countably generated,
ultrahomogeneous, and has age `K`.
-/
structure IsFraisseLimit [Countable (Σ l, L.Functions l)] [Countable M] : Prop where
  protected ultrahomogeneous : IsUltrahomogeneous L M
  protected age : L.age M = K

variable {M}

/-- Any embedding from a finitely generated `S` to an ultrahomogeneous structure `M`
can be extended to an embedding from any structure with an embedding to `M`. -/
/-
**FirstOrder.Language.IsUltrahomogeneous.extend_embedding** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.IsUltrahomogeneous`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M],   L.IsUlt
rahomogeneous M →     ∀ {S : Type u_1} [inst_1 : L.Structure S],       FirstOrde
r.Language.Structure.FG L S →         ∀ {T : Type u_2} [inst_2 : L.Structure T] 
[h : Nonempty (L.Embedding T M)] (f : L.Embedding S M)           (g : L.Embeddin
g S T), ∃ f', f = f'.comp g
参数：L.Embedding T M；f : L.Embedding S M；g : L.Embedding S T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.FG.range`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N],   Fir
stOrder.Language.Structure.F…
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Hom.mem_range`：mem_range {f : M ->[L] N} {x} : x in 
range f ↔ exists y, f y = x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Equiv.injective`：injective (f : M ≃[L] N) : Function
.Injective f
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FirstOrder.Language.Equiv.apply_symm_apply`：apply_symm_apply (f : M ≃[L]
 N) (a : N) : f (f.symm a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Any embedding from a finitely generated `S` to an ultrahomogeneous structure `M`
can be extended to an embedding from any structure with an embedding to `M`.
-/
theorem IsUltrahomogeneous.extend_embedding (M_homog : L.IsUltrahomogeneous M) {S : Type*}
    [L.Structure S] (S_FG : FG L S) {T : Type*} [L.Structure T] [h : Nonempty (T ↪[L] M)]
    (f : S ↪[L] M) (g : S ↪[L] T) :
    ∃ f' : T ↪[L] M, f = f'.comp g := by
  let ⟨r⟩ := h
  let s := r.comp g
  let ⟨t, eq⟩ := M_homog s.toHom.range (S_FG.range s.toHom) (f.comp s.equivRange.symm.toEmbedding)
  use t.toEmbedding.comp r
  change _ = t.toEmbedding.comp s
  ext x
  have eq' := congr_fun (congr_arg DFunLike.coe eq) ⟨s x, Hom.mem_range.2 ⟨x, rfl⟩⟩
  simp only [Embedding.comp_apply,
    coe_subtype] at eq'
  simp only [Embedding.comp_apply, ← eq', Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq]
  apply (Embedding.equivRange (Embedding.comp r g)).injective
  ext
  simp only [Equiv.apply_symm_apply, Embedding.equivRange_apply, s]

/-- A countably generated structure is ultrahomogeneous if and only if any equivalence between
finitely generated substructures can be extended to any element in the domain. -/
/-
**FirstOrder.Language.isUltrahomogeneous_iff_IsExtensionPair** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language`。
形式化陈述：isUltrahomogeneous_iff_IsExtensionPair (M_CG : CG L M) : L.IsUltrahomogene
ous M ↔ L.IsExtensionPair M M
参数：M_CG : CG L M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `FirstOrder.Language.IsUltrahomogeneous.extend_embedding`：∀ {L : FirstOrd
er.Language} {M : Type w} [inst : L.Structure M],   L.IsUltrahomogeneous M →    
 ∀ {S : Type u_1} [inst_1 : L.Structure S],  …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `FirstOrder.Language.Substructure.FG.sup`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] {N₁ N₂ : L.Substructure M},   N₁.FG → N₂.FG →
 (N₁ ⊔ N₂).FG
· 使用定理 `FirstOrder.Language.Substructure.fg_closure_singleton`：fg_closure_single
ton (x : M) : FG (closure L ({x} : Set M))
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FirstOrder.Language.equiv_between_cg`：equiv_between_cg (M_cg : Structure
.CG L M) (N_cg : Structure.CG L N) (g : L.FGEquiv M N) (ext_dom : L.IsExtensionP
air M N) (ext_cod : L.IsEx…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Embedding.subtype_equivRange`：subtype_equivRange (f 
: M ↪[L] N) : (subtype _).comp f.equivRange.toEmbedding = f

--- 原说明 ---
A countably generated structure is ultrahomogeneous if and only if any equivalen
ce between
finitely generated substructures can be extended to any element in the domain.
-/
theorem isUltrahomogeneous_iff_IsExtensionPair (M_CG : CG L M) : L.IsUltrahomogeneous M ↔
    L.IsExtensionPair M M := by
  constructor
  · intro M_homog ⟨f, f_FG⟩ m
    let S := f.dom ⊔ closure L {m}
    have dom_le_S : f.dom ≤ S := le_sup_left
    let ⟨f', eq_f'⟩ := M_homog.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
      ((subtype _).comp f.toEquiv.toEmbedding) (inclusion dom_le_S) (h := ⟨subtype _⟩)
    refine ⟨⟨⟨S, f'.toHom.range, f'.equivRange⟩, f_FG.sup (fg_closure_singleton _)⟩,
      subset_closure.trans (le_sup_right : _ ≤ S) (mem_singleton m), ⟨dom_le_S, ?_⟩⟩
    ext
    simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, coe_subtype, eq_f',
      Embedding.equivRange_apply, Substructure.coe_inclusion]
  · intro h S S_FG f
    let ⟨g, ⟨dom_le_dom, eq⟩⟩ :=
      equiv_between_cg M_CG M_CG ⟨⟨S, f.toHom.range, f.equivRange⟩, S_FG⟩ h h
    use g
    simp only [Embedding.subtype_equivRange] at eq
    rw [← eq]
    ext
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**FirstOrder.Language.IsUltrahomogeneous.amalgamation_age** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.IsUltrahomogeneous`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M],   L.IsUlt
rahomogeneous M → FirstOrder.Language.Amalgamation (L.age M)
参数：L.age M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.FG.range`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N],   Fir
stOrder.Language.Structure.F…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `FirstOrder.Language.Substructure.FG.sup`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] {N₁ N₂ : L.Substructure M},   N₁.FG → N₂.FG →
 (N₁ ⊔ N₂).FG
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `FirstOrder.Language.Embedding.ext_iff`：∀ {L : FirstOrder.Language} {M : 
Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   {f g : L
.Embedding M N}, f = g ↔ ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.coe_inclusion`：coe_inclusion {S T : L.S
ubstructure M} (h : S <= T) : (inclusion h : S -> T) = Set.inclusion h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.Equiv.symm_apply_apply`：symm_apply_apply (f : M ≃[L]
 N) (a : M) : f.symm (f a) = a
· 使用定理 `FirstOrder.Language.Embedding.comp_apply`：comp_apply (g : N ↪[L] P) (f :
 M ↪[L] N) (x : M) : g.comp f x = g (f x)
· 使用定理 `FirstOrder.Language.Equiv.coe_toEmbedding`：coe_toEmbedding (f : M ≃[L] N
) : (f.toEmbedding : M -> N) = (f : M -> N)
· 使用定理 `FirstOrder.Language.Embedding.equivRange_apply`：equivRange_apply (f : M 
↪[L] N) (x : M) : (f.equivRange x : N) = f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsUltrahomogeneous.amalgamation_age (h : L.IsUltrahomogeneous M) :
    Amalgamation (L.age M) := by
  rintro N P Q NP NQ ⟨Nfg, ⟨-⟩⟩ ⟨Pfg, ⟨PM⟩⟩ ⟨Qfg, ⟨QM⟩⟩
  obtain ⟨g, hg⟩ := h (PM.comp NP).toHom.range (Nfg.range _)
    ((QM.comp NQ).comp (PM.comp NP).equivRange.symm.toEmbedding)
  let s := (g.toHom.comp PM.toHom).range ⊔ QM.toHom.range
  refine ⟨Bundled.of s,
    Embedding.comp (Substructure.inclusion le_sup_left)
      (g.toEmbedding.comp PM).equivRange.toEmbedding,
    Embedding.comp (Substructure.inclusion le_sup_right) QM.equivRange.toEmbedding,
    ⟨(fg_iff_structure_fg _).1 (FG.sup (Pfg.range _) (Qfg.range _)), ⟨Substructure.subtype _⟩⟩, ?_⟩
  ext n
  apply Subtype.ext
  have hgn := (Embedding.ext_iff.1 hg) ((PM.comp NP).equivRange n)
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply,
    Substructure.coe_subtype, Embedding.equivRange_apply] at hgn
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding]
  erw [Substructure.coe_inclusion, Substructure.coe_inclusion]
  simp only [Embedding.equivRange_apply, hgn]
  -- This used to be `simp only [...]` before https://github.com/leanprover/lean4/pull/2644
  erw [Embedding.comp_apply, Equiv.coe_toEmbedding,
    Embedding.equivRange_apply]
  simp
/-
**FirstOrder.Language.IsUltrahomogeneous.age_isFraisse** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.IsUltrahomogeneous`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] [Countable
 M],   L.IsUltrahomogeneous M → FirstOrder.Language.IsFraisse (L.age M)
参数：L.age M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.age.nonempty`：∀ {L : FirstOrder.Language} (M : Type 
w) [inst : L.Structure M], (L.age M).Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `FirstOrder.Language.age.countable_quotient`：∀ {L : FirstOrder.Language} 
(M : Type w) [inst : L.Structure M] [h : Countable M], (Quotient.mk' '' L.age M)
.Countable
· 使用定理 `FirstOrder.Language.age.hereditary`：∀ {L : FirstOrder.Language} (M : Typ
e w) [inst : L.Structure M], FirstOrder.Language.Hereditary (L.age M)
· 使用定理 `FirstOrder.Language.age.jointEmbedding`：∀ {L : FirstOrder.Language} (M :
 Type w) [inst : L.Structure M], FirstOrder.Language.JointEmbedding (L.age M)
· 使用定理 `FirstOrder.Language.IsUltrahomogeneous.amalgamation_age`：∀ {L : FirstOrd
er.Language} {M : Type w} [inst : L.Structure M],   L.IsUltrahomogeneous M → Fir
stOrder.Language.Amalgamation (L.age M)
-/
theorem IsUltrahomogeneous.age_isFraisse [Countable M] (h : L.IsUltrahomogeneous M) :
    IsFraisse (L.age M) :=
  ⟨age.nonempty M, fun _ hN => hN.1, age.countable_quotient M,
    age.hereditary M, age.jointEmbedding M, h.amalgamation_age⟩

namespace IsFraisseLimit

/-- If a class has a Fraïssé limit, it must be Fraïssé. -/
/-
**FirstOrder.Language.IsFraisseLimit.isFraisse** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.IsFraisseLimit`。
形式化陈述：isFraisse [Countable (Σ l, L.Functions l)] [Countable M] (h : IsFraisseLim
it K M) : IsFraisse K
参数：Σ l, L.Functions l；h : IsFraisseLimit K M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.IsFraisseLimit.age`：∀ {L : FirstOrder.Language} {K :
 Set (CategoryTheory.Bundled L.Structure)} {M : Type w} [inst : L.Structure M]  
 [inst_1 : Countable ((l : ℕ…
· 使用定理 `FirstOrder.Language.IsUltrahomogeneous.age_isFraisse`：∀ {L : FirstOrder.
Language} {M : Type w} [inst : L.Structure M] [Countable M],   L.IsUltrahomogene
ous M → FirstOrder.Language.IsFraisse (L.a…
· 使用定理 `FirstOrder.Language.IsFraisseLimit.ultrahomogeneous`：∀ {L : FirstOrder.L
anguage} {K : Set (CategoryTheory.Bundled L.Structure)} {M : Type w} [inst : L.S
tructure M]   [inst_1 : Countable ((l : ℕ…

--- 原说明 ---
If a class has a Fraïssé limit, it must be Fraïssé.
-/
theorem isFraisse [Countable (Σ l, L.Functions l)] [Countable M] (h : IsFraisseLimit K M) :
    IsFraisse K :=
  (congr rfl h.age).mp h.ultrahomogeneous.age_isFraisse

variable {K} {N : Type w} [L.Structure N]
variable [Countable (Σ l, L.Functions l)] [Countable M] [Countable N]
variable (hM : IsFraisseLimit K M) (hN : IsFraisseLimit K N)

include hM hN
/-
**FirstOrder.Language.IsFraisseLimit.isExtensionPair** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.IsFraisseLimit`。
形式化陈述：∀ {L : FirstOrder.Language} {K : Set (CategoryTheory.Bundled L.Structure)}
 {M : Type w} [inst : L.Structure M]   {N : Type w} [inst_1 : L.Structure N] [in
st_2 : Countable ((l : ℕ) × L.Functions l)] [inst_3 : Countable M]   [inst_4 : C
ountable N],   FirstOrder.Language.IsFraisseLimit K M → FirstOrder.Language.IsFr
aisseLimit K N → L.IsExtensionPair M N
参数：CategoryTheory.Bundled L.Structure；(l : ℕ) × L.Functions l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.FG.sup`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] {N₁ N₂ : L.Substructure M},   N₁.FG → N₂.FG →
 (N₁ ⊔ N₂).FG
· 使用定理 `FirstOrder.Language.Substructure.fg_closure_singleton`：fg_closure_single
ton (x : M) : FG (closure L ({x} : Set M))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.IsFraisseLimit.age`：∀ {L : FirstOrder.Language} {K :
 Set (CategoryTheory.Bundled L.Structure)} {M : Type w} [inst : L.Structure M]  
 [inst_1 : Countable ((l : ℕ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `FirstOrder.Language.IsUltrahomogeneous.extend_embedding`：∀ {L : FirstOrd
er.Language} {M : Type w} [inst : L.Structure M],   L.IsUltrahomogeneous M →    
 ∀ {S : Type u_1} [inst_1 : L.Structure S],  …
· 使用定理 `FirstOrder.Language.IsFraisseLimit.ultrahomogeneous`：∀ {L : FirstOrder.L
anguage} {K : Set (CategoryTheory.Bundled L.Structure)} {M : Type w} [inst : L.S
tructure M]   [inst_1 : Countable ((l : ℕ…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem isExtensionPair : L.IsExtensionPair M N := by
  intro ⟨f, f_FG⟩ m
  let S := f.dom ⊔ closure L {m}
  have S_FG : S.FG := f_FG.sup (Substructure.fg_closure_singleton _)
  have S_in_age_N : ⟨S, inferInstance⟩ ∈ L.age N := by
    rw [hN.age, ← hM.age]
    exact ⟨(fg_iff_structure_fg S).1 S_FG, ⟨subtype _⟩⟩
  have nonempty_S_N : Nonempty (S ↪[L] N) := S_in_age_N.2
  let ⟨g, g_eq⟩ := hN.ultrahomogeneous.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
    ((subtype f.cod).comp f.toEquiv.toEmbedding) (inclusion (le_sup_left : _ ≤ S))
  refine ⟨⟨⟨S, g.toHom.range, g.equivRange⟩, S_FG⟩,
    subset_closure.trans (le_sup_right : _ ≤ S) (mem_singleton m), ⟨le_sup_left, ?_⟩⟩
  ext
  simp [S, g_eq]

/-- The Fraïssé limit of a class is unique, in that any two Fraïssé limits are isomorphic. -/
/-
**FirstOrder.Language.IsFraisseLimit.nonempty_equiv** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.IsFraisseLimit`。
形式化陈述：nonempty_equiv : Nonempty (M ≃[L] N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `FirstOrder.Language.Substructure.fg_bot`：fg_bot : (⊥ : L.Substructure M)
.FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.IsFraisseLimit.age`：∀ {L : FirstOrder.Language} {K :
 Set (CategoryTheory.Bundled L.Structure)} {M : Type w} [inst : L.Structure M]  
 [inst_1 : Countable ((l : ℕ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.equiv_between_cg`：equiv_between_cg (M_cg : Structure
.CG L M) (N_cg : Structure.CG L N) (g : L.FGEquiv M N) (ext_dom : L.IsExtensionP
air M N) (ext_cod : L.IsEx…
· 使用定理 `FirstOrder.Language.Structure.cg_of_countable`：cg_of_countable [Countabl
e M] : CG L M
· 使用定理 `FirstOrder.Language.IsFraisseLimit.isExtensionPair`：∀ {L : FirstOrder.La
nguage} {K : Set (CategoryTheory.Bundled L.Structure)} {M : Type w} [inst : L.St
ructure M]   {N : Type w} [inst_1 : L.St…

--- 原说明 ---
The Fraïssé limit of a class is unique, in that any two Fraïssé limits are isomo
rphic.
-/
theorem nonempty_equiv : Nonempty (M ≃[L] N) := by
  let S : L.Substructure M := ⊥
  have S_fg : FG L S := (fg_iff_structure_fg _).1 Substructure.fg_bot
  obtain ⟨_, ⟨emb_S : S ↪[L] N⟩⟩ : ⟨S, inferInstance⟩ ∈ L.age N := by
    rw [hN.age, ← hM.age]
    exact ⟨S_fg, ⟨subtype _⟩⟩
  let v : M ≃ₚ[L] N := {
    dom := S
    cod := emb_S.toHom.range
    toEquiv := emb_S.equivRange
  }
  exact ⟨Exists.choose (equiv_between_cg cg_of_countable cg_of_countable
    ⟨v, ((Substructure.fg_iff_structure_fg _).2 S_fg)⟩ (hM.isExtensionPair hN)
      (hN.isExtensionPair hM))⟩

end IsFraisseLimit

namespace empty

set_option backward.isDefEq.respectTransparency.types false in
/-- Any countable infinite structure in the empty language is a Fraïssé limit of the class of finite
structures. -/
/-
**FirstOrder.Language.empty.isFraisseLimit_of_countable_infinite** 是 Mathlib 中的一
个定理，位于命名空间 `FirstOrder.Language.empty`。
形式化陈述：isFraisseLimit_of_countable_infinite (M : Type*) [Countable M] [Infinite M
] [Language.empty.Structure M] : IsFraisseLimit { S : Bundled Language.empty.Str
ucture | Finite S } M where age
参数：M : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Countable.countable_functions`：∀ {L : FirstOrder.Lan
guage} [h : Countable L.Symbols], Countable ((l : ℕ) × L.Functions l)
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `FirstOrder.Language.instIsRelationalEmpty`：FirstOrder.Language.empty.IsR
elational
· 使用定理 `FirstOrder.Language.instIsAlgebraicEmpty`：FirstOrder.Language.empty.IsAl
gebraic
· 使用定理 `FirstOrder.Language.Substructure.FG.finite`：∀ {L : FirstOrder.Language} 
{M : Type u_1} [inst : L.Structure M] [L.IsRelational] {S : L.Substructure M},  
 S.FG → Finite ↥S
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Set.Finite.infinite_compl`：∀ {α : Type u} [Infinite α] {s : Set α}, s.Fi
nite → sᶜ.Infinite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `FirstOrder.Language.Structure.FG.range`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N],   Fir
stOrder.Language.Structure.F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `FirstOrder.Language.strongHomClassEmpty`：∀ {M : Type w} {N : Type w'} [i
nst : FirstOrder.Language.empty.Structure M]   [inst_1 : FirstOrder.Language.emp
ty.Structure N] {F : Type u_3…
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `FirstOrder.Language.StrongHomClass.toEquiv_toFun`：∀ {L : FirstOrder.Lang
uage} {F : Type u_3} {M : Type u_4} {N : Type u_5} [inst : L.Structure M] [inst_
1 : L.Structure N]   [inst_2 : EquivLi…
· 使用定理 `Equiv.sumCompl_symm_apply_of_pos`：sumCompl_symm_apply_of_pos {α} {p : α 
-> Prop} [DecidablePred p] {a : α} (h : p a) : (sumCompl p).symm a = Sum.inl ⟨a,
 h⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `FirstOrder.Language.Embedding.equivRange_toEquiv_apply`：∀ {L : FirstOrde
r.Language} {M : Type w} {N : Type u_1} [inst : L.Structure M] [inst_1 : L.Struc
ture N]   (f : L.Embedding M N) (a : M),   f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Any countable infinite structure in the empty language is a Fraïssé limit of the
 class of finite
structures.
-/
theorem isFraisseLimit_of_countable_infinite
    (M : Type*) [Countable M] [Infinite M] [Language.empty.Structure M] :
    IsFraisseLimit { S : Bundled Language.empty.Structure | Finite S } M where
  age := by
    ext S
    simp only [age, Structure.fg_iff_finite, mem_ofPred_eq, and_iff_left_iff_imp]
    intro hS
    simp
  ultrahomogeneous S hS f := by
    classical
    have : Finite S := hS.finite
    have : Infinite { x // x ∉ S } := ((Set.toFinite _).infinite_compl).to_subtype
    have : Finite f.toHom.range := (((Substructure.fg_iff_structure_fg S).1 hS).range _).finite
    have : Infinite { x // x ∉ f.toHom.range } := ((Set.toFinite _).infinite_compl).to_subtype
    refine ⟨StrongHomClass.toEquiv (f.equivRange.subtypeCongr nonempty_equiv_of_countable.some), ?_⟩
    ext x
    simp [Equiv.subtypeCongr]

/-- The class of finite structures in the empty language is Fraïssé. -/
/-
**FirstOrder.Language.empty.isFraisse_finite** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.empty`。
形式化陈述：isFraisse_finite : IsFraisse { S : Bundled.{w} Language.empty.Structure | 
Finite S }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.IsFraisseLimit.isFraisse`：isFraisse [Countable (Σ l,
 L.Functions l)] [Countable M] (h : IsFraisseLimit K M) : IsFraisse K
· 使用定理 `FirstOrder.Language.Countable.countable_functions`：∀ {L : FirstOrder.Lan
guage} [h : Countable L.Symbols], Countable ((l : ℕ) × L.Functions l)
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `FirstOrder.Language.instIsRelationalEmpty`：FirstOrder.Language.empty.IsR
elational
· 使用定理 `FirstOrder.Language.instIsAlgebraicEmpty`：FirstOrder.Language.empty.IsAl
gebraic
· 使用定理 `instCountableULift`：∀ {β : Type v} [Countable β], Countable (ULift.{u, v
} β)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `FirstOrder.Language.empty.isFraisseLimit_of_countable_infinite`：isFraiss
eLimit_of_countable_infinite (M : Type*) [Countable M] [Infinite M] [Language.em
pty.Structure M] : IsFraisseLimit { S : Bundled Lang…
· 使用定理 `instInfiniteULift`：∀ {α : Type v} [Infinite α], Infinite (ULift.{u, v} α
)
· 使用定理 `instInfiniteNat`：Infinite ℕ

--- 原说明 ---
The class of finite structures in the empty language is Fraïssé.
-/
theorem isFraisse_finite : IsFraisse { S : Bundled.{w} Language.empty.Structure | Finite S } := by
  have : Language.empty.Structure (ULift ℕ : Type w) := emptyStructure
  exact (isFraisseLimit_of_countable_infinite (ULift ℕ)).isFraisse

end empty

end Language

end FirstOrder

