Vivado 2018.2 installation in a container
==================================

1. Create Dockerfile in a separate folder with the following content:
    ```
    FROM ubuntu:20.04
    ARG DEBIAN_FRONTEND=noninteractive
    ENV TZ=Europe/London
    RUN apt-get update && apt-get install -y gedit libtinfo5 libncurses5-dev iproute2
    # gedit is useful to test that graphics passthrough is working
    # iproute2 is useful to check mac address
    # libtinfo5 and libncurses5 seem to be needed for Vivado
    # With ubuntu 22.04 vivado 2018.2 exit quickly after start
    # Ubuntu 20.04 seems to be more stable
    ```

2. Run `podman build --tag vivado .` in that folder
3. To get graphics passthrough with X, you'll need to create xauth file.
   You can use the following script that I called gen_xauthority.sh:
    ```
    #!/usr/bin/env bash

    CONTAINERNAME="${1:-vivado}"
    touch .Xauthority && \
    xauth -f .Xauthority add $CONTAINERNAME/unix:0 MIT-MAGIC-COOKIE-1 1ee043605d90ec22c2975d91a6b0798b && \
    xauth                add $CONTAINERNAME/unix:0 MIT-MAGIC-COOKIE-1 1ee043605d90ec22c2975d91a6b0798b
    # hex numbers are random
    ```
4. To run the container you can use the following script that I called run.sh:
    ```
    #!/usr/bin/env bash

    ./gen_xauthority.sh && \
    exec \
    podman run -it --rm -v .Xauthority:/root/.Xauthority:ro -v /tmp/.X11-unix:/tmp/.X11-unix:ro -v .:/mnt -e "DISPLAY" -h vivado --workdir /mnt --network podman --mac-address e2:fa:df:52:9f:78 vivado
    # mac-address is random, you can use any
    ```
5. Inside container run Vivado 2018.2 installer, and point it to /mnt folder (as / will be destroyed)
