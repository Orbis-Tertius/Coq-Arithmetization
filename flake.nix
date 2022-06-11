{
  description = "A Flake for building coq and providing devShells for the coq-tinyram project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    nix-doom-emacs.url = "github:nix-community/nix-doom-emacs";
    emacs.url = "github:cmacrae/emacs";
  };

  outputs =
    { self
    , nixpkgs
    , emacs
    , nix-doom-emacs
    }:
    let
      # Generate a user-friendly version number.
      version = builtins.substring 0 8 self.lastModifiedDate;
      # System types to support.
      supportedSystems = [ "x86_64-linux" "aarch64-linux" ];
      # Helper function to generate an attrset '{ x86_64-linux = f "x86_64-linux"; ... }'.
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      # Nixpkgs instantiated for supported system types.
      nixpkgsFor = forAllSystems (system:
        import nixpkgs {
          inherit system;
          overlays = [ self.overlay ];
        });
    in
    {
      herculesCI.ciSystems = [ "x86_64-linux" ];
      overlay = final: prev: { };
      # the default devShell used when running `nix develop`
      devShell = forAllSystems (system: self.devShells.${system}.defaultShell);
      devShells = forAllSystems (system:
        let
          pkgs = nixpkgsFor."${system}";
        in
        {
          # In case we don't want to provide an editor, this defaultShell will
          # provide only coq packages we need.
          defaultShell = pkgs.mkShell {
            buildInputs = with pkgs; [
              vampire
              eprover
              ocaml
              dune_2
              coqPackages.coq
              coqPackages.mathcomp
              coqPackages.ssreflect
              coqPackages.mathcomp-fingroup
              coqPackages.mathcomp-algebra
              coqPackages.mathcomp-solvable
              coqPackages.mathcomp-field
              coqPackages.coqhammer
            ];
          };
          # This is the defaultShell, but overriden to add one additional buildInput,
          # vscodium!
          vscodium = self.devShells.${system}.defaultShell.overrideAttrs (old: {
            buildInputs =
              let
                vscodeWithCoq = pkgs.vscode-with-extensions.override {
                  vscode = pkgs.vscodium;
                  vscodeExtensions = pkgs.vscode-utils.extensionsFromVscodeMarketplace [
                    {
                      name = "VSCoq";
                      publisher = "maximedenes";
                      version = "0.3.6";
                      sha256 = "sha256-b0gCaEzt5yAj53oLFZSXSD3bum9J1fYes/uf9+OlUek=";
                    }
                    {
                      name = "Haskell";
                      publisher = "haskell";
                      version = "2.1.3";
                      sha256 = "sha256-OWV8i1XPO1BUc66nIIKoJmzs0D95O0+FJE1hxpYqPBw=";
                    }
                    {
                      name = "language-haskell";
                      publisher = "justusadam";
                      version = "3.3.0";
                      sha256 = "sha256-2rlomc4qjca1Mv5lxgT/4AARzuG8e4kgshielpBeBYk=";
                    }
                  ];
                };
              in
              old.buildInputs
              ++ [
                vscodeWithCoq
              ];
          });
          # This is the defaultShell, but overriden to add one additional buildInput,
          # emacs!
          emacs = self.devShells.${system}.defaultShell.overrideAttrs (old: {
            buildInputs =
              let
                doom-emacsWithCoq = nix-doom-emacs.package.${system} {
                  doomPrivateDir = ./nix/doom.d;
                };
              in
              old.buildInputs
              ++ [
                doom-emacsWithCoq
              ];
          });
        });
    };
}
