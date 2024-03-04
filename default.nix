{ mkDerivation, standard-library }:

mkDerivation {
  pname = "catt-agda";
  version = "0.1";

  src = ./.;

  buildInputs = [ standard-library ];
}
