{ system ? builtins.currentSystem
, pkgs ? import <nixpkgs> { inherit system; config = {}; overlays = []; }
}:
pkgs.mkShell {
  buildInputs = with pkgs; [ coqPackages_8_17.category-theory ];
  shellHooks = ''
    echo "-R ${pkgs.coqPackages_8_17.category-theory} Catgeory" >> _CoqProject
  '';
}
