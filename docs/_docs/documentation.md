---
title: Documentation
permalink: /docs/documentation/
---

The documentation is hosted in the docs folder and is re-created on pushes to master. When contributing to the project please consider the [contribution guide](https://github.com/pulp-platform/ariane/blob/master/CONTRIBUTING.md).

## Timing Diagrams

The current scheme allows you to insert timing diagrams written in [WaveJSON](https://github.com/drom/wavedrom/wiki/WaveJSON).

Insert [WaveJSON](https://github.com/drom/wavedrom/wiki/WaveJSON) source inside HTML ``<body>`` wrapped with ``<script>`` tag:

```html
<script type="WaveDrom">
{ signal : [
  { name: "clk",  wave: "p......" },
  { name: "bus",  wave: "x.34.5x",   data: "head body tail" },
  { name: "wire", wave: "0.1..0." },
]}
</script>
```

<script type="WaveDrom">
{ signal : [
  { name: "clk",  wave: "p......" },
  { name: "bus",  wave: "x.34.5x",   data: "head body tail" },
  { name: "wire", wave: "0.1..0." },
]}
</script>
