module Everything where

import Catt.Prelude
import Catt.Prelude.Properties

import Catt.Syntax.Base
import Catt.Syntax
import Catt.Syntax.Bundles
import Catt.Syntax.Properties
import Catt.Syntax.Complexity

import Catt.Variables
import Catt.Variables.Properties

import Catt.Globular
import Catt.Globular.Properties

import Catt.Pasting
import Catt.Pasting.Properties

import Catt.Suspension
import Catt.Suspension.Properties
import Catt.Suspension.Pasting

import Catt.Wedge
import Catt.Wedge.Properties
import Catt.Wedge.Pasting

import Catt.Discs
import Catt.Discs.Properties
import Catt.Discs.Pasting

import Catt.Tree
import Catt.Tree.Properties
import Catt.Tree.Pasting

import Catt.Tree.Path
import Catt.Tree.Path.Properties

import Catt.Tree.Structured
import Catt.Tree.Structured.Properties
import Catt.Tree.Structured.Globular
import Catt.Tree.Structured.Globular.Properties
import Catt.Tree.Structured.Construct
import Catt.Tree.Structured.Construct.Properties
import Catt.Tree.Structured.ToTerm

import Catt.Tree.Boundary
import Catt.Tree.Boundary.Properties

import Catt.Tree.Standard
import Catt.Tree.Standard.Properties

import Catt.Tree.Insertion
import Catt.Tree.Insertion.Properties

import Catt.Dyck
import Catt.Dyck.Properties
import Catt.Dyck.Pasting
import Catt.Dyck.Pruning
import Catt.Dyck.Pruning.Properties
import Catt.Dyck.FromTree

import Catt.Typing.Base
import Catt.Typing
import Catt.Typing.Rule
import Catt.Typing.Rule.Properties
import Catt.Typing.Properties.Base
import Catt.Typing.Properties.Lifting
import Catt.Typing.Properties.Substitution
import Catt.Typing.Properties.Substitution.Suspended
import Catt.Typing.Properties
import Catt.Typing.Properties.Conversion

import Catt.Globular.Typing
import Catt.Pasting.Typing
import Catt.Suspension.Typing
import Catt.Wedge.Typing
import Catt.Discs.Typing
import Catt.Tree.Typing
import Catt.Tree.Path.Typing
import Catt.Tree.Structured.Typing
import Catt.Tree.Structured.Typing.Properties
import Catt.Tree.Boundary.Typing
import Catt.Tree.Standard.Typing
import Catt.Tree.Insertion.Typing
import Catt.Dyck.Typing
import Catt.Dyck.Pruning.Typing


import Catt.Typing.DiscRemoval.Rule
import Catt.Typing.DiscRemoval
import Catt.Typing.DiscRemoval.Properties
import Catt.Typing.DiscRemoval.Typed
import Catt.Typing.Properties
import Catt.Typing.EndoCoherenceRemoval.Rule
import Catt.Typing.EndoCoherenceRemoval
import Catt.Typing.EndoCoherenceRemoval.Properties
import Catt.Typing.EndoCoherenceRemoval.Typed
import Catt.Typing.Insertion.Rule
import Catt.Typing.Insertion
import Catt.Typing.Insertion.Equality
import Catt.Typing.Insertion.Typed
import Catt.Typing.Pruning.Rule
import Catt.Typing.Pruning
import Catt.Typing.Pruning.Typed


import Catt.Support
import Catt.Support.Typing
import Catt.Support.Properties
import Catt.Support.Context

import Catt.Suspension.Support
import Catt.Wedge.Support
import Catt.Discs.Support
import Catt.Tree.Support
import Catt.Tree.Structured.Support
import Catt.Tree.Structured.Support.Properties
import Catt.Tree.Boundary.Support
import Catt.Tree.Standard.Support

import Catt.Typing.Properties.Support
import Catt.Typing.Structured.Support
import Catt.Typing.DiscRemoval.Support
import Catt.Typing.EndoCoherenceRemoval.Support
import Catt.Typing.Insertion.Support
import Catt.Typing.Pruning.Support

import Catt.Typing.Weak
import Catt.Typing.Strict.Units
import Catt.Typing.Strict.UA
