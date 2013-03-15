(function ($) {
  $(function () {
    setTimeout(function () {
      dims = $('.item').map(function () {
        var
          $this = $(this)
        , w = $this.outerWidth() + 2
        , h = $this.outerHeight() + 2
        ;
        return {
          s: $this
        , w: w
        , h: h
        };
      }).get();
      dims.sort(function (a, b) {
        return b.h - a.h;
      });
      //console.log('##### INITIAL #####');
      //$.each(dims, function (i, d) { console.log(d.w + 'w:h' + d.h); });
      var packer = new Packer(3508, 2480);
      packer.fit(dims);
      //console.log('##### AFTER #####');
      //$.each(dims, function (i, el) {
        //if (el.fit) {
          ////console.log(el.fit.x + 'x:y' + el.fit.y);
          //el.s.css({
            //position: 'absolute'
          //, left: el.fit.x
          //, top: el.fit.y
          //});
        //} else {
          //console.log('did not fit!!');
          //console.log(el.s.text());
        //}
      //});
      //console.log('done!');
      $('h1, h2, h3, h4, h5, h6').addClass('dontend');
      $('#container').columnize({ columns: 7 });
    }, 1000);
    setTimeout(function () { console.log('foobar!'); }, 2000);
    prettyPrint();
    $(window).resize();
  });
}(jQuery));
