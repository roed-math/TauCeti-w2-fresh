/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Continuous

set_option warningAsError false

/-!
# Lookahead stubs for `sheaf-h-pullback`

These are lookahead stubs for the supplier `sheaf-h-pullback` (SchemeAndStackFoundations §2.1),
whose pullback `Sheaf.H.pullback` has landed and whose higher direct images are in the open pull
request 27242. They are stated as that pull request states them, in
`TauCeti/CategoryTheory/Sites/Continuous.lean`, and are to be replaced by the landed declarations.
Only the declaration consumed by the Leray target is restated: the additivity of the pushforward
of sheaves along a continuous functor, without which its right derived functors, the higher
direct images, are not defined.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (u : C ⥤ D)
  (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K]

/-- Stub: the pushforward of sheaves along a continuous functor is additive. -/
instance [Preadditive A] : (u.sheafPushforwardContinuous A J K).Additive :=
  sorry

end CategoryTheory.Functor
