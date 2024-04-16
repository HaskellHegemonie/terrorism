{ system ? builtins.currentSystem
, pkgs ? import <nixpkgs> { inherit system; config ={}; overlays = []; }
}:
pkgs.mkShell {
  buildInputs = with pkgs; [ lean4 ];
  # shellHooks = ''
  #   export LEAN_PATH=${pkgs.lean3}/lib/lean:${builtins.toString ./.}
  # '';
}
