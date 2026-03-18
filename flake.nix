{
  description = "groth16-verifier — formal verification of a Groth16 verifier in Lean 4";

  inputs = {
    nixpkgs.url     = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # elan: the Lean version manager (analogous to rustup)
        # It reads lean-toolchain and downloads the correct Lean build.
        elan = pkgs.elan;

        # curl and git are needed by Lake (the Lean build system)
        # to fetch Mathlib and its dependencies.
        buildDeps = with pkgs; [ curl git cacert ];

        # Optional: VS Code with the Lean 4 extension pre-configured
        vscode-with-lean = pkgs.vscode-with-extensions.override {
          vscodeExtensions = with pkgs.vscode-extensions; [
            leanprover.lean4
          ];
        };

      in {
        # ── Development shell ──────────────────────────────────────────────────
        devShells.default = pkgs.mkShell {
          name = "groth16-verifier";

          packages = buildDeps ++ [
            elan            # manages the Lean toolchain
            pkgs.jq         # useful for inspecting lake-manifest.json
          ];

          # Tell elan where to store toolchains in the Nix sandbox
          ELAN_HOME = ".elan";

          # Needed for SSL certificate validation when Lake fetches packages
          GIT_SSL_CAINFO = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
          SSL_CERT_FILE  = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";

          shellHook = ''
            echo ""
            echo "  ╔══════════════════════════════════════════╗"
            echo "  ║  groth16-verifier — Lean 4 proof project  ║"
            echo "  ╚══════════════════════════════════════════╝"
            echo ""
            echo "  Lean toolchain : $(cat lean-toolchain 2>/dev/null || echo 'see lean-toolchain')"
            echo ""
            echo "  Quick start:"
            echo "    lake build              # build everything"
            echo "    lake exe cache get      # fetch prebuilt Mathlib oleans"
            echo ""
            echo "  First-time setup takes ~20 min to download Mathlib oleans."
            echo ""
          '';
        };

        # ── VS Code shell (includes the Lean 4 extension) ─────────────────────
        devShells.vscode = pkgs.mkShell {
          name = "groth16-verifier-vscode";
          packages = buildDeps ++ [ elan vscode-with-lean ];
          inherit (self.devShells.${system}.default) ELAN_HOME GIT_SSL_CAINFO SSL_CERT_FILE shellHook;
        };
      }
    );
}
