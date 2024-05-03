# Build the docs

## For PDF
```
pip install -r requirements.txt
make latexpdf
evince build/latex/*.pdf
```

## HTML
```
pip install -r requirements.txt
make html
firefox build/html/index.html
```
