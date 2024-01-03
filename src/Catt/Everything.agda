module Catt.Everything where

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

import Catt.Connection
import Catt.Connection.Properties
import Catt.Connection.Pasting

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

import Catt.Tree.Canonical
import Catt.Tree.Canonical.Properties

import Catt.Tree.Insertion
import Catt.Tree.Insertion.Properties

import Catt.Dyck
import Catt.Dyck.Properties
import Catt.Dyck.Pruning
import Catt.Dyck.Pruning.Properties
import Catt.Dyck.FromTree

import Catt.Typing.Base
import Catt.Typing.Rule
import Catt.Typing
import Catt.Typing.Properties.Base
import Catt.Typing.Properties.Lifting
import Catt.Typing.Properties.Substitution
import Catt.Typing.Properties.Substitution.Suspended
import Catt.Typing.Properties
import Catt.Typing.Properties.Conversion

import Catt.Globular.Typing
import Catt.Pasting.Typing
import Catt.Suspension.Typing
import Catt.Connection.Typing
import Catt.Discs.Typing
import Catt.Tree.Typing
import Catt.Tree.Path.Typing
import Catt.Tree.Structured.Typing
import Catt.Tree.Structured.Typing.Properties
import Catt.Tree.Boundary.Typing
import Catt.Tree.Canonical.Typing
import Catt.Tree.Insertion.Typing
import Catt.Dyck.Typing
import Catt.Dyck.Pruning.Typing

import Catt.Typing.DiscRemoval
import Catt.Typing.DiscRemoval.Base
import Catt.Typing.Properties
import Catt.Typing.EndoCoherenceRemoval
import Catt.Typing.EndoCoherenceRemoval.Base
import Catt.Typing.EndoCoherenceRemoval.Properties
import Catt.Typing.Insertion
import Catt.Typing.Insertion.Base
import Catt.Typing.Insertion.Equality
import Catt.Typing.Pruning
import Catt.Typing.Pruning.Base

import Catt.Support
import Catt.Support.Properties
import Catt.Support.Context

import Catt.Suspension.Support
import Catt.Connection.Support
import Catt.Discs.Support
import Catt.Tree.Support
import Catt.Tree.Structured.Support
import Catt.Tree.Boundary.Support
import Catt.Tree.Canonical.Support

import Catt.Typing.Properties.Support
import Catt.Tree.Structured.Support.Typed
-- import Catt.Tree.Insertion.Support

import Catt.Typing.Weak
import Catt.Typing.Strict.Units
import Catt.Typing.Strict.UA
