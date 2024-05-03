import os
import codecs
from setuptools import setup, find_packages

import riscv_config

# Base directory of package
here = os.path.abspath(os.path.dirname(__file__))


def read(*parts):
    with codecs.open(os.path.join(here, *parts), 'r') as fp:
        return fp.read()


#Long Description
with open("README.rst", "r") as fh:
    long_description = fh.read()

setup(name="riscv_config",
      version=riscv_config.__version__,
      description="RISC-V Configuration Validator",
      long_description=long_description,
      classifiers=[
          "Programming Language :: Python :: 3.6",
          "License :: OSI Approved :: BSD License",
          "Development Status :: 4 - Beta"
      ],
      url='https://github.com/riscv/riscv-config',
      author='InCore Semiconductors Pvt. Ltd.',
      author_email='neelgala@incoresemi.com',
      license='BSD-3-Clause',
      packages=find_packages(),
      install_package_data=True,
      package_dir={'riscv_config': 'riscv_config/'},
      package_data={'riscv_config': ['schemas/*']},
      install_requires=['Cerberus>=1.3.1', 'ruamel.yaml>=0.17.16', 'pyyaml==5.2'],
      python_requires=">=3.7.0",
      entry_points={
          "console_scripts": ["riscv-config=riscv_config.main:main"],
      })
