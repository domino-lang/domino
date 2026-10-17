Right.comp.ssp assigns the import c.f in two separate compose blocks.
Composition validation rejects the second assignment with DuplicateEdgeDefinitionError,
pointing at the second f. The error also applies when both assignments use the same destination.
Removing the second compose block makes the project valid.
