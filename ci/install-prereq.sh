#!/bin/bash

echo 'deb http://download.opensuse.org/repositories/home:/phiwag:/edatools/xUbuntu_20.04/ /' | sudo tee /etc/apt/sources.list.d/home:phiwag:edatools.list
curl -fsSL https://download.opensuse.org/repositories/home:phiwag:edatools/xUbuntu_20.04/Release.key | gpg --dearmor | sudo tee /etc/apt/trusted.gpg.d/home_phiwag_edatools.gpg > /dev/null

sudo apt update
sudo apt install device-tree-compiler libfl-dev help2man

