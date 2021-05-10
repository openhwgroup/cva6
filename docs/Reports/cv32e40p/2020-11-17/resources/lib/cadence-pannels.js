var nested1 = null; //set  as true for 1 nested splitter
var nested2 = null;

	function toggleLiveResizing () {
		$.each( $.layout.config.borderPanes, function (i, pane) {
			var o = myLayout.options[ pane ];
			o.livePaneResizing = !o.livePaneResizing;
		});
	};

	function toggleStateManagement ( skipAlert, mode ) {
		if (!$.layout.plugins.stateManagement) return;

		var options	= myLayout.options.stateManagement
		,	enabled	= options.enabled // current setting
		;
		if ($.type( mode ) === "boolean") {
			if (enabled === mode) return; // already correct
			enabled	= options.enabled = mode
		}
		else
			enabled	= options.enabled = !enabled; // toggle option

		if (!enabled) { // if disabling state management...
			myLayout.deleteCookie(); // ...clear cookie so will NOT be found on next refresh
			if (!skipAlert)
				alert( 'This layout will reload as the options specify \nwhen the page is refreshed.' );
		}
		else if (!skipAlert)
			alert( 'This layout will save & restore its last state \nwhen the page is refreshed.' );


	};

	// set EVERY 'state' here so will undo ALL layout changes
	// used by the 'Reset State' button: myLayout.loadState( stateResetSettings )
	var stateResetSettings = {
		north__size:		"auto"
	,	north__initClosed:	false
	,	north__initHidden:	false
	,	south__size:		"auto"
	,	south__initClosed:	false
	,	south__initHidden:	false
	,	west__size:			200
	,	west__initClosed:	false
	,	west__initHidden:	false
	,	east__size:			300
	,	east__initClosed:	false
	,	east__initHidden:	false
	};

	var myLayout;


	$(document).ready(function () {

		// this layout could be created with NO OPTIONS - but showing some here just as a sample...
		// myLayout = $('body').layout(); -- syntax with No Options

		myLayout = $("body > #container > #content").layout({

		//	reference only - these options are NOT required because 'true' is the default
			closable:					true	// pane can open & close
		,	resizable:					true	// when open, pane can be resized
		,	slidable:					true	// when closed, pane can 'slide' open over other panes - closes on mouse-out
		,	livePaneResizing:			true

		//	some resizing/toggling settings
		,north: {
				size:				300
			,	resizable:			true
			,	togglerLength_open:	0
			,	spacing_open:		1 /* cosmetic only */
			,	initHidden:			true
			,	onhide_end:			function () {
					$("#pane4-open").slideDown();
					$("#pane4-closed").hide();
				}
			,	onshow_start:		function () {
					$("#pane4-open").hide();
					$("#pane4-closed").slideDown();
				}
		}
	//	,	south__resizable:			false	// OVERRIDE the pane-default of 'resizable=true'
	//	,	south__spacing_open:		0		// no resizer-bar when open (zero height)
	//	,	south__spacing_closed:		20		// big resizer-bar when open (zero height)
        ,	south__minSize:	100
  		,	south__size:			200	// 'fast' animation when resizing west-pane



		//	some pane-size settings
		,	west__minSize:				100
		,	east__size:                 .5
            ,	west__size:                 .5
		,	east__minSize:				100
	//	,	east__maxSize:				.5 // 50% of layout width
		,	center__minWidth:			100
            ,	center__size:           .5

		//	some pane animation settings
//		,	west__animatePaneSizing:	false
		,	west__fxSpeed_size:			"fast"	// 'fast' animation when resizing west-pane
		,	west__fxSpeed_open:			700	// 1-second animation when opening west-pane
	//	,	west__fxSettings_open:		{ easing: "easeOutBounce" } // 'bounce' effect when opening
	//	,	west__fxName_close:			"none"	// NO animation when closing west-pane

		//	enable showOverflow on west-pane so CSS popups will overlap north pane
//		,	west__showOverflowOnHover:	true

		//	enable state management
		,	stateManagement__enabled:	true // automatic cookie load & save enabled by default

		,	showDebugMessages:			true // log and/or display messages from debugging & testing code
		});


        if(nested1 === true) {
           myLayout1 = $('body  > #container > #content > .ui-layout-center').layout({

		//	reference only - these options are NOT required because 'true' is the default
			closable:					true	// pane can open & close
		,	resizable:					true	// when open, pane can be resized
		,	slidable:					true	// when closed, pane can 'slide' open over other panes - closes on mouse-out
		,	livePaneResizing:			true

		//	some resizing/toggling settings
		,	north__slidable:			false	// OVERRIDE the pane-default of 'slidable=true'
		,	north__togglerLength_closed: '100%'	// toggle-button is full-width of resizer-bar
		,	north__spacing_closed:		20		// big resizer-bar when open (zero height)
	//	,	south__resizable:			false	// OVERRIDE the pane-default of 'resizable=true'
	//	,	south__spacing_open:		0		// no resizer-bar when open (zero height)
	//	,	south__spacing_closed:		20		// big resizer-bar when open (zero height)

		//	some pane-size settings
		,	west__minSize:				100
        ,   west_size:                 .5
	    ,	east__size:					00
		,	east__minSize:				100
//		,	east__maxSize:				.5 // 50% of layout width
		,	center__minWidth:			100
         ,	center__size:              .3
        ,	south__minSize:	100
        ,   north__size:			200	// 'fast' animation when resizing west-pane
  		,	south__size:			200	// 'fast' animation when resizing west-pane


		//	some pane animation settings
		,	west__animatePaneSizing:	false
		,	west__fxSpeed_size:			"fast"	// 'fast' animation when resizing west-pane
		,	west__fxSpeed_open:			700	// 1-second animation when opening west-pane
		,	west__fxSettings_open:		{ easing: "easeOutBounce" } // 'bounce' effect when opening
		,	west__fxName_close:			"none"	// NO animation when closing west-pane

		//	enable showOverflow on west-pane so CSS popups will overlap north pane
		,	west__showOverflowOnHover:	false

        //	some pane animation settings

		//	enable state management
		,	stateManagement__enabled:	true // automatic cookie load & save enabled by default

		,	showDebugMessages:			true // log and/or display messages from debugging & testing code
		});


        }

		// if there is no state-cookie, then DISABLE state management initially
		var cookieExists = !$.isEmptyObject( myLayout.readCookie() );
		if (!cookieExists) toggleStateManagement( true, false );




		/*
		 *	DISABLE TEXT-SELECTION WHEN DRAGGING (or even _trying_ to drag!)
		 *	this functionality will be included in RC30.80
		 */
		$.layout.disableTextSelection = function(){
			var $d	= $(document)
			,	s	= 'textSelectionDisabled'
			,	x	= 'textSelectionInitialized'
			;
			if ($.fn.disableSelection) {
				if (!$d.data(x)) // document hasn't been initialized yet
					$d.on('mouseup', $.layout.enableTextSelection ).data(x, true);
				if (!$d.data(s))
					$d.disableSelection().data(s, true);
			}
			//console.log('$.layout.disableTextSelection');
		};
		$.layout.enableTextSelection = function(){
			var $d	= $(document)
			,	s	= 'textSelectionDisabled';
			if ($.fn.enableSelection && $d.data(s))
				$d.enableSelection().data(s, false);
			//console.log('$.layout.enableTextSelection');
		};
		$(".ui-layout-resizer")
			.disableSelection() // affects only the resizer element
			.on('mousedown', $.layout.disableTextSelection ); // affects entire document

	    myLayout.sizePane("north", 145);



               if(nested2===true) {
                   var myLayout2 = $('body  > #container > #content > .ui-layout-west').layout({

                      		//	reference only - these options are NOT required because 'true' is the default
       			closable:					true	// pane can open & close
       		,	resizable:					true	// when open, pane can be resized
       		,	slidable:					true	// when closed, pane can 'slide' open over other panes - closes on mouse-out
       		,	livePaneResizing:			true

       		//	some resizing/toggling settings
       		,	north__slidable:			false	// OVERRIDE the pane-default of 'slidable=true'
       		,	north__togglerLength_closed: '100%'	// toggle-button is full-width of resizer-bar
       		,	north__spacing_closed:		20		// big resizer-bar when open (zero height)
       	//	,	south__resizable:			false	// OVERRIDE the pane-default of 'resizable=true'
       	//	,	south__spacing_open:		0		// no resizer-bar when open (zero height)
       	//	,	south__spacing_closed:		20		// big resizer-bar when open (zero height)
               ,	south__minSize:	100
         		,	south__size:			200	// 'fast' animation when resizing west-pane



       		//	some pane-size settings
       		,	west__minSize:				100
       	        ,	west__size:                 .5
       		,	east__minSize:				100
       	//	,	east__maxSize:				.5 // 50% of layout width
       		,	center__minWidth:			100
                   ,	center__size:           .5

       		//	some pane animation settings
       //		,	west__animatePaneSizing:	false
       		,	west__fxSpeed_size:			"fast"	// 'fast' animation when resizing west-pane
       		,	west__fxSpeed_open:			700	// 1-second animation when opening west-pane
       	//	,	west__fxSettings_open:		{ easing: "easeOutBounce" } // 'bounce' effect when opening
       	//	,	west__fxName_close:			"none"	// NO animation when closing west-pane

       		//	enable showOverflow on west-pane so CSS popups will overlap north pane
       		,	west__showOverflowOnHover:	false

       		//	enable state management
       		,	stateManagement__enabled:	true // automatic cookie load & save enabled by default

       		,	showDebugMessages:			true // log and/or display messages from debugging & testing code
       		});

                   //myLayout2.sizePane("west", .5);
               }

 	});
