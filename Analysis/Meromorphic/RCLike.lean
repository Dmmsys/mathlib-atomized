/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.RCLike.Basic

/-!
# Meromorphic Functions over the Real and Complex Numbers

This file gathers results on meromorphic functions specifict to the real and complex numbers.
-/

public section

open Set Complex

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall` / 定理 `Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall`

English:
theorem Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall
  given: {f : 𝕜 -> E} (hf : Meromorphic f)
  proof: by
  simpa using (meromorphicOn_univ.2 hf).exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ

中文:
定理 亚纯.存在_meromorphicOrderAt_ne_top_iff_对任意
  条件: {f : 𝕜 -> E} (hf : 亚纯 f)
  证明: by
  simpa using (meromorphicOn_univ.2 hf).exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ

Depends on / 依赖: exists_meromorphicOrderAt_ne_top_iff_forall, isConnected_univ, meromorphicOn_univ
-/
theorem Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall {f : 𝕜 -> E} (hf : Meromorphic f) :
    (exists u, meromorphicOrderAt f u != ⊤) ↔ (forall u, meromorphicOrderAt f u != ⊤) := by
  simpa using (meromorphicOn_univ.2 hf).exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ
