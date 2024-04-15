##########
Quickstart
##########

This doc is meant to serve as a quick-guide to setup RISCV-CONFIG and perform a \
sample validation of target specifications.

Install Python
==============

RISCV-CONFIG requires `pip` and `python` (>=3.6) to be available on your system. 

Ubuntu
------

Ubuntu 17.10 and 18.04 by default come with python-3.6.9 which is sufficient for using riscv-config.

If you are are Ubuntu 16.10 and 17.04 you can directly install python3.6 using the Universe
repository::

  $ sudo apt-get install python3.6
  $ pip3 install --upgrade pip

If you are using Ubuntu 14.04 or 16.04 you need to get python3.6 from a Personal Package Archive 
(PPA)::

  $ sudo add-apt-repository ppa:deadsnakes/ppa
  $ sudo apt-get update
  $ sudo apt-get install python3.6 -y 
  $ pip3 install --upgrade pip

You should now have 2 binaries: ``python3`` and ``pip3`` available in your $PATH. 
You can check the versions as below::

  $ python3 --version
  Python 3.6.9
  $ pip3 --version
  pip 20.1 from <user-path>.local/lib/python3.6/site-packages/pip (python 3.6)

Centos:7
--------
The CentOS 7 Linux distribution includes Python 2 by default. However, as of CentOS 7.7, Python 3 
is available in the base package repository which can be installed using the following commands::

  $ sudo yum update -y
  $ sudo yum install -y python3
  $ pip3 install --upgrade pip

For versions prior to 7.7 you can install python3.6 using third-party repositories, such as the 
IUS repository::

  $ sudo yum update -y
  $ sudo yum install yum-utils
  $ sudo yum install https://centos7.iuscommunity.org/ius-release.rpm
  $ sudo yum install python36u
  $ pip3 install --upgrade pip

You can check the versions::

  $ python3 --version
  Python 3.6.8
  $ pip --version
  pip 20.1 from <user-path>.local/lib/python3.6/site-packages/pip (python 3.6)


Using Virtualenv for Python 
---------------------------

Many a times folks face issues in installing and managing python versions, which is actually a 
major issue as many gui elements in Linux use the default python versions. In which case installing
python3.6 using the above methods might break other software. We thus advise the use of **pyenv** to
install python3.6.

For Ubuntu and CentosOS, please follow the steps here: https://github.com/pyenv/pyenv#basic-github-checkout

RHEL users can find more detailed guides for virtual-env here: https://developers.redhat.com/blog/2018/08/13/install-python3-rhel/#create-env

Once you have pyenv installed do the following to install python 3.6.0::

  $ pyenv install 3.6.0
  $ pip3 install --upgrade pip
  $ pyenv shell 3.6.0
  
You can check the version in the **same shell**::

  $ python --version
  Python 3.6.0
  $ pip --version
  pip 20.1 from <user-path>.local/lib/python3.6/site-packages/pip (python 3.6)


Install RISCV-CONFIG
====================

.. note:: If you are using a virtual environment make sure to enable that environment before
  performing the following steps.

.. code-block:: bash

  $ pip3 install riscv-config

To update an already installed version of RISCV-CONFIG to the latest version:

.. code-block:: bash

  $ pip3 install -U riscv-config

To checkout a specific version of riscv-config:

.. code-block:: bash

  $ pip3 install riscv-config--1.x.x

Once you have RISCV-CONFIG installed, executing ``riscv-config --help`` should print the following 
output ::

    riscv-config [-h] [--version] [--isa_spec YAML] [--platform_spec YAML]
                        [--work_dir DIR] [--verbose]
    
    RISC-V Configuration Validator
    
    optional arguments:
      --isa_spec YAML, -ispec YAML
                            The YAML which contains the ISA specs.
      --platform_spec YAML, -pspec YAML
                            The YAML which contains the Platfrorm specs.
      --verbose             debug | info | warning | error
      --version, -v         Print version of RISCV-CONFIG being used
      --work_dir DIR        The name of the work dir to dump the output files to.
      -h, --help            show this help message and exit

RISCV-CONFIG for Developers
===========================

Clone the repository from git and install required dependencies. 

.. note::  you will still need python (>=3.6.0) and pip. 
  If you are using `pyenv` as mentioned above, make sure to enable that environment before
  performing the following steps.

.. code-block:: bash

  $ git clone https://github.com/riscv/riscv-config.git
  $ cd riscv-config
  $ pip3 install -r requirements.txt

Executing ``python -m riscv-config.main --help`` should display the same help message as above.

Usage Example
=============

.. code-block:: bash

    $ riscv-config -ispec examples/rv32i_isa.yaml -pspec examples/rv32i_platform.yaml

Executing the above command should display the following on the terminal:

.. code-block:: bash

  [INFO]    : Input-ISA file
  [INFO]    : Loading input file: /scratch/git-repo/github/riscv-config/examples/rv32i_isa.yaml
  [INFO]    : Load Schema /scratch/git-repo/github/riscv-config/riscv-config/schemas/schema_isa.yaml
  [INFO]    : Initiating Validation
  [INFO]    : No Syntax errors in Input ISA Yaml. :)
  [INFO]    : Initiating post processing and reset value checks.
  [INFO]    : Dumping out Normalized Checked YAML: /scratch/git-repo/github/riscv-config/riscv_config_work/rv32i_isa_checked.yaml
  [INFO]    : Input-Platform file
  [INFO]    : Loading input file: /scratch/git-repo/github/riscv-config/examples/rv32i_platform.yaml
  [INFO]    : Load Schema /scratch/git-repo/github/riscv-config/riscv_config/schemas/schema_platform.yaml
  [INFO]    : Initiating Validation
  [INFO]    : No Syntax errors in Input Platform Yaml. :)
  [INFO]    : Dumping out Normalized Checked YAML: /scratch/git-repo/github/riscv-config/riscv_config_work/rv32i_platform_checked.yaml
  

