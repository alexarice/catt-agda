{
  description = "Formalisation of Catt with semistrictness in Agda";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    all-agda.url = "github:alexarice/all-agda";
  };

  outputs = { self, nixpkgs, flake-utils, all-agda }: flake-utils.lib.eachDefaultSystem (system: let
    pkgs = import nixpkgs { inherit system; overlays = [ all-agda.overlay.${system} ]; };
  in {
    devShell = pkgs.mkShell {
      nativeBuildInputs = with pkgs; [
        (agda-2_6_4.withPackages (p: [ p.standard-library ]))
      ];
    };

    packages = rec {
      default = catt-agda;
      catt-agda = pkgs.agdaPackages-2_6_4.callPackage ./default.nix { };
    };
  });
}
