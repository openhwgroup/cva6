# Docker Image for CVA6

This folder contains the Dockerfile to build the docker image for CVA6. You can
do so by executing:

```
docker build . -f util/docker/Dockerfile.ubuntu -t openhwgroup/cva6:latest
```

To run the image

```
docker run -it -v `pwd`:/repo --env="DISPLAY=docker.for.mac.host.internal:0" openhwgroup/cva6
```

This will open a prompt where you `cd /repo` and execute the `make` commands.
