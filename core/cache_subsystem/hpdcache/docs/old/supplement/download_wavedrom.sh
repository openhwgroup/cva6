#!/bin/bash
WAVEDROM_ARCHIVE=wavedrom-editor-v2.9.1-linux-x64
WAVEDROM_URL=https://github.com/wavedrom/wavedrom.github.io/releases/download/v2.9.1/${WAVEDROM_ARCHIVE}.tar.gz

WAVEDROM_CLI=package/wavedrom/wavedrom-cli.js
WAVEDROM_CLI_URL=https://github.com/wavedrom/cli/releases/download/v0.3.1/wavedrom-cli.js

echo -e 'Download the archive'
if [[ ! -e ${WAVEDROM_ARCHIVE}.tar.gz ]]; then
    wget -q ${WAVEDROM_URL}
fi

echo -e 'Decompress the archive'
if [[ ! -e package/wavedrom/${WAVEDROM_ARCHIVE} ]]; then
    mkdir -p package/wavedrom
    tar xzf ${WAVEDROM_ARCHIVE} -C package/wavedrom
fi

echo -e 'Download wavedrom command-line client'
if [[ ! -e ${WAVEDROM_CLI} ]]; then
    wget -q -O ${WAVEDROM_CLI} ${WAVEDROM_CLI_URL}
fi
