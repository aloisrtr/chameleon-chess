let
  pkgs = import (fetchTarball("channel:nixpkgs-unstable")) {};
in pkgs.mkShell {
  buildInputs = with pkgs; [ 
  linuxPackages_latest.perf 
  pkg-config
  fontconfig
  openssl
  vulkan-tools
  vulkan-headers
  vulkan-loader
  vulkan-validation-layers
  wgpu-utils
  ];
  LD_LIBRARY_PATH = "${pkgs.openssl.out}/lib:${pkgs.vulkan-headers}/lib:${pkgs.vulkan-loader}/lib";
}
