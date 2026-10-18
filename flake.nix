{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          hpkgs = pkgs.haskell.packages.ghc9123;
        in {
          default = pkgs.mkShell {
            packages = [
              hpkgs.ghc
              pkgs.cabal-install
              hpkgs.haskell-language-server
            ];
          };
        });
    };
}
