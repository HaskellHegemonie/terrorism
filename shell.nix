{ system ? builtins.currentSystem
, pkgs ? import <nixpkgs> { inherit system; config ={}; overlays = []; }
}:
pkgs.mkShell {
  buildInputs = with pkgs; [ coq_8_13 ];
}
