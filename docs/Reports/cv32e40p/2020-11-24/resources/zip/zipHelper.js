var loadedFileName = null;
var zipFile = null;

function getJsonFile(jsonFileName, zipFileName) {

    if (loadedFileName === zipFileName) {
        return getJsonFileLoaded(jsonFileName);
    }

    var output;

    JSZipUtils.getBinaryContent(zipFileName, function (err, data) {

        if (err) {
            alert(err);
            throw err; // or handle err

        }

        zipFile = new JSZip();

        zipFile.loadAsync(data).then(function (zip) {
            loadedFileName = zipFileName;
            return getJsonFileLoaded(jsonFileName);
        });

    });

}

function getJsonFileLoaded(jsonFileName) {

    zipFile.file(jsonFileName).async("uint8array").then(function (json) {

        //var tmpJson = new TextDecoder("utf-8").decode(json);
        var tmpJson = "";
        for (var i = 0; i < json.length; i++) {
            tmpJson += String.fromCharCode(parseInt(json[i]));
        }
        //This output will hold the json from the zip
        try {
            output = JSON.parse(tmpJson);
        } catch (e) {
            output = null;
        }
        //alert(output['cover_group_items'][0]['All Average Grd']);
        //console.log('cover_group_items at zero for All Average Grd is ' + output['cover_group_items'][0]['All Average Grd']);
        nodeData = output;
        showNodeData(nodeData);

    });

}


function getJsonTreeChildFile(jsonFileName, zipFileName, treeData) {


    var output;

    JSZipUtils.getBinaryContent(zipFileName, function (err, data) {

        if (err) {
            alert(err);
            throw err; // or handle err

        }

        zipFile = new JSZip();

        zipFile.loadAsync(data).then(function (zip) {
            loadedFileName = zipFileName;
            getChildJsonFileLoaded(jsonFileName, treeData);
        });

    });

}


function getChildJsonFileLoaded(jsonFileName, data) {
    zipFile.file(jsonFileName).async("uint8array").then(function (json) {

        //var tmpJson = new TextDecoder("utf-8").decode(json);
        var tmpJson = "";
        for (var i = 0; i < json.length; i++) {
            tmpJson += String.fromCharCode(parseInt(json[i]));
        }
        //This output will hold the json from the zip
        try {
            output = JSON.parse(tmpJson);
        } catch (e) {
            output = null;
        }

        if (output != null &&
            (data.node.children == undefined || data.node.children.length == 0)) {
            data.node.addChildren(output);
        }
    });
}

function showSubFolders(fileName, data) {
    getJsonTreeChildFile(getChildFileName(fileName), getChildZipDirName(fileName) + "zipChildData0.zip", data);
}

function getChildFileName(fileName) { //"childDir1/childData0.json"
    return fileName.substr(fileName.indexOf("/") + 1, fileName.length);
}

function getChildZipDirName(fileName) { //"childDir1/childData0.json"
    return fileName.substr(0, fileName.indexOf("/") + 1);
}