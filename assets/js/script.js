(function ($) {
  $(function () {
    setTimeout(function () {
      dims = $('.item').map(function () {
        var
          $this = $(this)
        , w = $this.outerWidth() + 10
        , h = $this.outerHeight() + 10
        ;
        return {
          s: $this
        , w: w
        , h: h
        };
      }).get();
      dims.sort(function (a, b) {
        return Math.max(a.w, a.h) - Math.max(b.w, b.h);
      });
      console.log('##### INITIAL #####');
      $.each(dims, function (i, d) { console.log(d.w + 'w:h' + d.h); });
      var packer = new Packer(3508, 2480);
      packer.fit(dims);
      console.log('##### AFTER #####');
      $.each(dims, function (i, el) {
        console.log(el.fit.x + 'x:y' + el.fit.y);
        el.s.css({
          position: 'absolute'
        , left: el.fit.x
        , top: el.fit.y
        });
      });
      console.log('done!');
    }, 100);
    setTimeout(function () { console.log('hej!'); }, 1000);
    $(window).resize();
  });
}(jQuery));
