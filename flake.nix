{
  description = "Formalisation of Catt with semistrictness in Agda";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    all-agda.url = "github:alexarice/all-agda";
  };

  outputs = { self, nixpkgs, flake-utils, all-agda }: flake-utils.lib.eachDefaultSystem (system: let
    pkgs = import nixpkgs { inherit system; overlays = [ all-agda.overlay.${system} ]; };
  in {
    test = 1;
    devShell = pkgs.mkShell {
      nativeBuildInputs = with pkgs; [
        cabal-install
        haskell-language-server
        haskellPackages.fix-whitespace
        (agda-2_6_3.withPackages (p: [ p.standard-library ]))
      ];
    };
  });
}
